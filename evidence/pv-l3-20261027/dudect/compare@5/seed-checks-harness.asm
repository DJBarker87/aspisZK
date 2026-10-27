pv_dudect::kernels::entropy::seed_check @ 0x38070
movdqu xmm0,XMMWORD PTR [rdi]
movdqu xmm1,XMMWORD PTR [rdi+0x10]
por    xmm1,xmm0
pxor   xmm0,xmm0
pcmpeqb xmm0,xmm1
pmovmskb eax,xmm0
xor    eax,0xffff
setne  al
ret
int3
int3
int3
int3
int3
int3
int3
int3
int3
int3
int3
int3
int3
int3
