#include <stddef.h>
int memcmp(const void *,const void *,size_t);
int s126_coupled_cmp(const unsigned char *,const unsigned char *,size_t);
int s126_coupled_memcmp(const void *a,const void *b,size_t n){if(n==688)return s126_coupled_cmp((const unsigned char *)a,(const unsigned char *)b,n);return memcmp(a,b,n);}
