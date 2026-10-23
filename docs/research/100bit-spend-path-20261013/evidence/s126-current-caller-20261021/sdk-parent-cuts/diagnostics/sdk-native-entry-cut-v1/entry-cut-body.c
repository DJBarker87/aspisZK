#include <stddef.h>
extern size_t s126_prefix_hits;
int memcmp(const void *,const void *,size_t);
int s126_entry_memcmp(const void *a,const void *b,size_t n){
 if(n==688){s126_prefix_hits+=1;return 1;}
 return memcmp(a,b,n);
}
