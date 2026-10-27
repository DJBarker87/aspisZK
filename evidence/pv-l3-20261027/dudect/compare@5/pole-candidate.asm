aspis_r1_cost_probe::ct_pole::all_slots_clear @ 0xc74e0
test   rsi,rsi
je     LOCAL+0x13c
shl    rsi,0x6
movq   xmm1,QWORD PTR [rcx]
pshufd xmm0,xmm1,0x44
movdqu xmm3,XMMWORD PTR [rcx]
pshufd xmm1,xmm1,0x11
pshufd xmm2,xmm3,0xaa
pshufd xmm3,xmm3,0xff
mov    al,0x1
xor    r8d,r8d
pcmpeqd xmm4,xmm4
xor    r10d,r10d
data16 cs nop WORD PTR [rax+rax*1+0x0]
mov    rcx,r10
shr    rcx,0x4
cmp    r10,0x400
je     LOCAL+0x13f
lea    r9,[r10+0x1]
movzx  r11d,WORD PTR [rdx+rcx*2]
and    r10d,0xf
xor    ecx,ecx
bt     r11d,r10d
setae  cl
movdqu xmm8,XMMWORD PTR [rdi+r8*1]
movdqu xmm5,XMMWORD PTR [rdi+r8*1+0x10]
movdqu xmm9,XMMWORD PTR [rdi+r8*1+0x20]
movdqu xmm6,XMMWORD PTR [rdi+r8*1+0x30]
pshufd xmm7,xmm8,0x55
movdqa xmm10,xmm5
punpckldq xmm10,xmm7
pshufd xmm11,xmm6,0x50
punpckldq xmm11,xmm9
movsd  xmm11,xmm10
pcmpeqd xmm11,xmm0
pxor   xmm11,xmm4
pshufd xmm10,xmm5,0x55
punpckldq xmm10,xmm8
pshufd xmm12,xmm9,0x50
movdqa xmm7,xmm6
punpckldq xmm7,xmm12
movsd  xmm7,xmm10
pcmpeqd xmm7,xmm1
pxor   xmm7,xmm4
por    xmm7,xmm11
punpckhdq xmm6,xmm9
punpckhdq xmm5,xmm8
movdqa xmm8,xmm5
punpcklqdq xmm8,xmm6
pcmpeqd xmm8,xmm2
pxor   xmm8,xmm4
punpckhqdq xmm5,xmm6
pcmpeqd xmm5,xmm3
pxor   xmm5,xmm4
por    xmm5,xmm8
movd   xmm6,ecx
pshufd xmm6,xmm6,0x0
por    xmm6,xmm5
por    xmm6,xmm7
pslld  xmm6,0x1f
movmskps ecx,xmm6
cmp    ecx,0xf
sete   cl
and    al,cl
add    r8,0x40
mov    r10,r9
cmp    rsi,r8
jne    LOCAL+0x40
ret
mov    al,0x1
ret
push   rax
lea    rdx,[RIP:anon.3225fe53cd26fbc09133d984eb8cbaf9.60.llvm.14277610391609414263]
mov    esi,0x40
mov    rdi,rcx
call   QWORD PTR [RIP:core::panicking::panic_bounds_check]
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
