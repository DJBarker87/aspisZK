pv_dudect::kernels::ct_pole::all_slots_clear @ 0x33880
push   rax
test   rsi,rsi
je     LOCAL+0x140
lea    rax,[rsi-0x401]
cmp    rax,0xfffffffffffffc00
jb     LOCAL+0x144
movq   xmm1,QWORD PTR [rcx]
pshufd xmm0,xmm1,0x44
movdqu xmm3,XMMWORD PTR [rcx]
pshufd xmm1,xmm1,0x11
pshufd xmm2,xmm3,0xaa
pshufd xmm3,xmm3,0xff
mov    al,0x1
xor    ecx,ecx
pcmpeqd xmm4,xmm4
data16 data16 data16 data16 data16 cs nop WORD PTR [rax+rax*1+0x0]
mov    r8,rcx
shr    r8,0x4
movzx  r9d,WORD PTR [rdx+r8*2]
mov    r10d,ecx
and    r10d,0xf
xor    r8d,r8d
bt     r9d,r10d
setae  r8b
movdqu xmm8,XMMWORD PTR [rdi]
movdqu xmm5,XMMWORD PTR [rdi+0x10]
movdqu xmm9,XMMWORD PTR [rdi+0x20]
movdqu xmm6,XMMWORD PTR [rdi+0x30]
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
movd   xmm6,r8d
pshufd xmm6,xmm6,0x0
por    xmm6,xmm5
por    xmm6,xmm7
pslld  xmm6,0x1f
movmskps r8d,xmm6
cmp    r8d,0xf
sete   r8b
and    al,r8b
inc    rcx
add    rdi,0x40
cmp    rsi,rcx
jne    LOCAL+0x50
pop    rcx
ret
mov    al,0x1
pop    rcx
ret
lea    rdx,[RIP:__frame_dummy_init_array_entry+0x3d8]
mov    edi,0x40
mov    esi,0x40
call   QWORD PTR [RIP:core::panicking::panic_bounds_check]
int3
int3
int3
int3
int3
