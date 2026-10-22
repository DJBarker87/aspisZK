#include <stddef.h>
void __CPROVER_havoc_slice(void *,size_t);
size_t s126_havoc_input(unsigned char *p,size_t n){__CPROVER_havoc_slice(p,n);return n;}
