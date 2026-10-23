#include <stddef.h>
int S2A_memcmp(const void *,const void *,size_t);
int (*S2A_keep)(const void *,const void *,size_t)=S2A_memcmp;
