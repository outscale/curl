/***************************************************************************
 *                                  _   _ ____  _
 *  Project                     ___| | | |  _ \| |
 *                             / __| | | | |_) | |
 *                            | (__| |_| |  _ <| |___
 *                             \___|\___/|_| \_\_____|
 *
 * Copyright (C) 1998 - 2020, Daniel Stenberg, <daniel@haxx.se>, et al.
 *
 * This software is licensed as described in the file COPYING, which
 * you should have received as part of this distribution. The terms
 * are also available at https://curl.haxx.se/docs/copyright.html.
 *
 * You may opt to use, copy, modify, merge, publish, distribute and/or sell
 * copies of the Software, and permit persons to whom the Software is
 * furnished to do so, under the terms of the COPYING file.
 *
 * This software is distributed on an "AS IS" basis, WITHOUT WARRANTY OF ANY
 * KIND, either express or implied.
 *
 ***************************************************************************/

#include "curl_setup.h"

#include "urldata.h"
#include "strcase.h"
#include "vauth/vauth.h"
#include "vauth/digest.h"
#include "http_v4_signature.h"
#include "curl_sha256.h"
#include "transfer.h"

/* The last 3 #include files should be in this order */
#include "curl_printf.h"
#include "curl_memory.h"
#include "memdebug.h"
#include <time.h>

static CURLcode hmac_sha256(const unsigned char *key, unsigned int keylen,
                            const unsigned char *data, unsigned int datalen,
                            unsigned char *output)
{
  HMAC_context *ctxt = Curl_HMAC_init(Curl_HMAC_SHA256, key, keylen);

  if(!ctxt)
    return CURLE_OUT_OF_MEMORY;

  /* printf("L: %d\n", datalen); */
  /* Update the digest with the given challenge */
  Curl_HMAC_update(ctxt, data, datalen);

  /* Finalise the digest */
  Curl_HMAC_final(ctxt, output);

  return CURLE_OK;
}

#define REGION_MAX_L 3

CURLcode Curl_output_v4_signature(struct connectdata *conn, bool proxy)
{
  CURLcode ret = CURLE_FAILED_INIT;
  char sk[45]; /* secret key is 40 chat long + 'OSC' + \0 */
  struct Curl_easy *data = conn->data;
  const char *customrequest = data->set.str[STRING_CUSTOMREQUEST];
  const char *surl = strstr(data->set.str[STRING_SET_URL], "://") + 3;
  char *host;
  struct tm *info;
  time_t rawtime;
  const char *provider = data->set.str[STRING_V4_PROVIDER];
  char low_provider[REGION_MAX_L + 1];
  char up_provider[REGION_MAX_L + 1];
  char mid_provider[REGION_MAX_L + 1];
  char *region;
  char *uri;
  char date_iso[17];
  char date[9];
  char date_str[64];
  const unsigned char *post_data = data->set.postfields ?
    data->set.postfields : "";
  const char *content_type = Curl_checkheaders(conn, "Content-Type");
  unsigned char sha_d[32];
  char sha_str[65];
  char *cred_scope;
  char *signed_headers;
  char request_type[REGION_MAX_L + sizeof("4_request")];
  char *canonical_hdr;
  char *canonical_request;
  char *str_to_sign;
  unsigned char tmp_sign0[32];
  unsigned char tmp_sign1[32];
  char *auth;
  char *tmp;
  int i;

  printf("Post Data '%s'\n", post_data);
  if(Curl_checkheaders(conn, "Authorization")) {
    /* Authorization alerady present, Bailing out */
    goto exit;
  }

  if(content_type) {
    content_type = strchr(content_type, ':') + 1;
    /* Skip whitespace now */
    while(*content_type == ' ' || *content_type == '\t')
      ++content_type;
  }

  tmp = strchr(provider, ':');
  if(tmp) {
    for(i = 0; provider != tmp; ++provider, ++i) {
      if(i > REGION_MAX_L)
        goto exit;
      up_provider[i] = (char)toupper(*provider);
    }
    up_provider[i] = 0;
    ++provider;
    for(i = 0; *provider; ++provider, ++i) {
      if(i > REGION_MAX_L)
        goto exit;
      low_provider[i] = (char)tolower(*provider);
      mid_provider[i] = i ? low_provider[i] : (char)toupper(*provider);
    }
    low_provider[i] = 0;
    mid_provider[i] = 0;
  }
  else if(strlen(provider) <= REGION_MAX_L) {
    for(i = 0; provider[i]; ++i) {
      low_provider[i] = (char)tolower(provider[i]);
      up_provider[i] = (char)toupper(low_provider[i]);
      mid_provider[i] = i ? low_provider[i] : up_provider[i];
    }
    low_provider[i] = 0;
    up_provider[i] = 0;
    mid_provider[i] = 0;
  }
  else {
    goto exit;
  }

  printf("%s %s %s\n", low_provider, up_provider, mid_provider);
  (void) proxy;
  time(&rawtime);
  info = localtime(&rawtime);
  if(!strftime(date_iso, 256, "%Y%m%dT%H%M%SZ", info)) {
    ret = CURLE_OUT_OF_MEMORY;
    goto exit;
  }
  memcpy(date, date_iso, 8);
  date[8] = 0;
  region = strdup(strchr(surl, '.') + 1);
  *strchr(region, '.') = 0;
  uri = strchr(surl, '/');
  host = strdup(surl);
  *strchr(host, '/') = 0;

  curl_msprintf(request_type, "%s4_request", low_provider);
  cred_scope = curl_maprintf("%s/%s/api/%s", date, region, request_type);
  if(content_type) {
    canonical_hdr = curl_maprintf(
      "content-type:%s\n"
      "host:%s\n"
      "x-%s-date:%s\n", content_type, host, low_provider, date_iso);
    signed_headers = curl_maprintf("content-type;host;x-%s-date",
                                   low_provider);
  }
  else {
    canonical_hdr = curl_maprintf(
      "host:%s\n"
      "x-%s-date:%s\n", host, low_provider, date_iso);
    signed_headers = curl_maprintf("host;x-%s-date", low_provider);
  }


  Curl_sha256it(sha_d, post_data);
  for(i = 0; i < 32; ++i) {
    curl_msprintf(sha_str + (i * 2), "%02x", sha_d[i]);
  }
  sha_str[64] = 0;

  canonical_request = curl_maprintf(
                     "%s\n" /* Methode */
                     "%s\n" /* uri */
                     "\n" /* querystring ? */
                     "%s\n" /* canonical_headers */
                     "%s\n" /* signed header */
                     "%s" /* SHA ! */,
                     customrequest,
                     uri, canonical_hdr, signed_headers, sha_str);

  printf("%s\n", canonical_request);
  Curl_sha256it(sha_d, (unsigned char *)canonical_request);
  for(i = 0; i < 32; ++i) {
    curl_msprintf(sha_str + (i * 2), "%02x", sha_d[i]);
  }

  str_to_sign = curl_maprintf("%s4-HMAC-SHA256\n"
                              "%s\n%s\n%s",
                              up_provider, date_iso, cred_scope, sha_str);

  curl_msprintf(sk, "%s4%s", up_provider, data->set.str[STRING_PASSWORD]);
  sk[44] = 0;

  hmac_sha256((unsigned char *)sk, 44, (unsigned char *)date,
              (unsigned int)strlen(date), tmp_sign0);
  for(i = 0; i < 32; ++i) {
    curl_msprintf(sha_str + (i * 2), "%02x", tmp_sign0[i]);
  }
  sha_str[64] = 0;

  hmac_sha256(tmp_sign0, 32, (void *)region,
              (unsigned int)strlen(region), tmp_sign1);
  hmac_sha256(tmp_sign1, 32, (void *)"api", sizeof("api") -1, tmp_sign0);
  hmac_sha256(tmp_sign0, 32, (void *)request_type,
              (unsigned int)strlen(request_type),
              tmp_sign1);
  hmac_sha256(tmp_sign1, 32, (void *)str_to_sign,
              (unsigned int)strlen(str_to_sign), tmp_sign0);

  for(i = 0; i < 32; ++i) {
    curl_msprintf(sha_str + (i * 2), "%02x", tmp_sign0[i]);
  }
  sha_str[64] = 0;

  auth = curl_maprintf("Authorization: %s4-HMAC-SHA256 Credential=%s/%s, "
                       "SignedHeaders=%s, Signature=%s",
                       up_provider, data->set.str[STRING_USERNAME], cred_scope,
                       signed_headers, sha_str);

  free(signed_headers);
  free(str_to_sign);
  free(canonical_hdr);
  free(cred_scope);
  free(region);
  free(host);
  curl_msprintf(date_str, "X-%s-Date: %s", mid_provider, date_iso);
  data->set.headers = curl_slist_append(data->set.headers, date_str);
  data->set.headers = curl_slist_append(data->set.headers, auth);
  free(auth);
  /* only send 1 request */
  data->state.authhost.done = 1;
  ret = CURLE_OK;
exit:
  return ret;
}

