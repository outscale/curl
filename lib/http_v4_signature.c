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

CURLcode Curl_output_v4_signature(struct connectdata *conn, bool proxy)
{
  CURLcode ret = CURLE_FAILED_INIT;
  char sk[45]; /* secret key is 40 chat long + 'OSC' + \0 */
  struct Curl_easy *data = conn->data;
  const char *surl = strstr(data->set.str[STRING_SET_URL], "://") + 3;
  char *host;
  struct tm *info;
  time_t rawtime;
  char *region;
  char *uri;
  char date_iso[17];
  char date[9];
  char date_str[64];
  const unsigned char *post_data = data->set.postfields ?
    data->set.postfields : "";
  unsigned char sha_d[32];
  char sha_str[65];
  char *cred_scope;
  char *canonical_hdr;
  char *canonical_request;
  char *str_to_sign;
  unsigned char tmp_sign0[32];
  unsigned char tmp_sign1[32];
  char *auth;
  void *tmp;
  int i;

  if(Curl_checkheaders(conn, "Authorization")) {
    goto exit; /* header alerady present, what to do ? */
  }

  (void) proxy;
  time(&rawtime);
  info = localtime(&rawtime);
  if(!strftime(date_iso, 256, "%Y%m%dT%H%M%SZ", info))
    goto exit;
  memcpy(date, date_iso, 8);
  date[8] = 0;
  region = strdup(strchr(surl, '.') + 1);
  *strchr(region, '.') = 0;
  uri = strchr(surl, '/');
  host = strdup(surl);
  *strchr(host, '/') = 0;

  Curl_sha256it(sha_d, post_data);
  for(i = 0; i < 32; ++i) {
    curl_msprintf(sha_str + (i * 2), "%02x", sha_d[i]);
  }
  sha_str[64] = 0;

  cred_scope = curl_maprintf("%s/%s/api/osc4_request", date, region);
  canonical_hdr = curl_maprintf(
    "content-type:application/json; charset=utf-8\n"
    "host:%s\n"
    "x-osc-date:%s\n", host, date_iso);
  canonical_request = curl_maprintf(
                     "%s\n" /* Methode */
                     "%s\n" /* uri */
                     "\n" /* querystring ? */
                     "%s\n" /* canonical_headers */
                     "content-type;host;x-osc-date\n" /* signed header */
                     "%s" /* SHA ! */,
                     "POST",
                     uri, canonical_hdr, sha_str);

  tmp = canonical_request;
  Curl_sha256it(sha_d, tmp);
  for(i = 0; i < 32; ++i) {
    curl_msprintf(sha_str + (i * 2), "%02x", sha_d[i]);
  }

  str_to_sign = curl_maprintf("OSC4-HMAC-SHA256\n"
                              "%s\n%s\n%s",
                              date_iso, cred_scope, sha_str);

  strcpy(sk, "OSC4");
  strncpy(sk + 4, data->set.str[STRING_PASSWORD], 40);
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
  hmac_sha256(tmp_sign0, 32, (void *)"osc4_request", sizeof("osc4_request") -1,
              tmp_sign1);
  hmac_sha256(tmp_sign1, 32, (void *)str_to_sign,
              (unsigned int)strlen(str_to_sign), tmp_sign0);

  for(i = 0; i < 32; ++i) {
    curl_msprintf(sha_str + (i * 2), "%02x", tmp_sign0[i]);
  }
  sha_str[64] = 0;

  auth = curl_maprintf("Authorization: OSC4-HMAC-SHA256 Credential=%s/%s, "
                       "SignedHeaders=content-type;host;x-osc-date,"
                       " Signature=%s",
                       data->set.str[STRING_USERNAME], cred_scope, sha_str);

  /* printf("ret: %s\n", auth); */

  free(str_to_sign);
  free(canonical_hdr);
  free(cred_scope);
  free(region);
  free(host);
  curl_msprintf(date_str, "X-Osc-Date: %s", date_iso);
  data->set.headers = curl_slist_append(data->set.headers, date_str);
  data->set.headers = curl_slist_append(data->set.headers, auth);
  free(auth);
  ret = CURLE_OK;
exit:
  return ret;
}

