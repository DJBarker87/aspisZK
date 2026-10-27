/* TEST ONLY: interpose precisely the client's 64-byte attempt entropy fill.
 * Never install this library or export LD_PRELOAD outside the fixture child.
 */
#define _GNU_SOURCE
#include <dlfcn.h>
#include <sys/types.h>
#include <stdatomic.h>
#include <unistd.h>
static _Atomic unsigned calls;
ssize_t getrandom(void *buf, size_t len, unsigned flags) {
    if (len == 64 && flags == 0) {
        unsigned k=atomic_fetch_add(&calls,1);
        unsigned char *p=buf;
        for (size_t i=0;i<len;i++) p[i]=(unsigned char)(i+1+17*k);
        static const char msg[]="N7_FIXTURE_ENTROPY_64\n";
        write(2,msg,sizeof(msg)-1);
        return (ssize_t)len;
    }
    ssize_t (*next)(void*,size_t,unsigned)=dlsym(RTLD_NEXT,"getrandom");
    return next(buf,len,flags);
}
