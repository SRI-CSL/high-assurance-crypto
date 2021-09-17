#include <stdlib.h>

extern void *sha3(const void *in, size_t inlen, void *md, int mdlen);

unsigned char *shake128_alloc(const unsigned char *in,unsigned long long inlen)
{
  unsigned char * out = (unsigned char *) malloc (32);
  sha3(in,inlen, out, 32);
  return out;
}
