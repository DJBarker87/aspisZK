// Explicit OS-world interpreter for a reproducible RAW caller probe.
// No production Rust function is replaced. Only libc getrandom replies are
// fixed; the second 64-byte call returns EIO. This is an interposition
// experiment, not a native entropy-law proof or a valid-witness counterexample.
#include <errno.h>
#include <stddef.h>
#include <stdint.h>
#include <stdlib.h>
#include <stdio.h>
#include <sys/types.h>
static unsigned draws64;
ssize_t getrandom(void *buffer, size_t length, unsigned flags) {
    (void)flags;
    unsigned seed = (unsigned)strtoul(getenv("PV_SEED") ? getenv("PV_SEED") : "1",NULL,10);
    if (length==64) {
        unsigned i=draws64++;
        fprintf(stderr,"PV_GETRANDOM position=%u length=64 seed=%u status=%s\n",i,seed,i ? "EIO" : "OK");
        if (i) {errno=EIO;return -1;}
    }
    uint64_t s=(uint64_t)seed+0x9e3779b97f4a7c15ULL;
    for(size_t i=0;i<length;i++) {s^=s>>12;s^=s<<25;s^=s>>27;((unsigned char*)buffer)[i]=(unsigned char)(s*2685821657736338717ULL>>56);}
    return (ssize_t)length;
}
