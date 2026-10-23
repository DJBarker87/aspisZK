#include <stddef.h>
extern size_t s126_prefix_hits;
int s126_cmp_choice(void);
int memcmp(const void *,const void *,size_t);
int s126_entry_memcmp(const void *a,const void *b,size_t n){
 if(n==688){s126_prefix_hits+=1;return s126_cmp_choice();}
 return memcmp(a,b,n);
}
void __CPROVER_havoc_slice(void *,size_t);
void s126_input_bytes(unsigned char *p,size_t n){__CPROVER_havoc_slice(p,n); }
