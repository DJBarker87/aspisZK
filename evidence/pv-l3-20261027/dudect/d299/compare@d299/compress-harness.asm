pv_dudect::kernels::prover_shared::compress_tagged_tuple @ 0x36ec0
push   rbp
push   r15
push   r14
push   r13
push   r12
push   rbx
mov    QWORD PTR [rsp-0x70],rdi
movd   xmm0,esi
test   rcx,rcx
je     LOCAL+0x5dd
mov    esi,DWORD PTR [r8+0xc]
mov    edi,DWORD PTR [r8+0x8]
mov    r13d,DWORD PTR [r8]
mov    r8d,DWORD PTR [r8+0x4]
lea    rax,[r8+r13*1]
mov    QWORD PTR [rsp-0x48],rax
lea    rax,[rdi+rsi*1]
mov    QWORD PTR [rsp-0x50],rax
lea    eax,[rdi+r13*1]
cmp    eax,0x7fffffff
lea    r9d,[r13+rdi*1-0x7fffffff]
cmovb  r9d,eax
lea    eax,[r8+rsi*1]
cmp    eax,0x7fffffff
lea    r10d,[r8+rsi*1-0x7fffffff]
cmovb  r10d,eax
mov    QWORD PTR [rsp-0x58],r9
mov    QWORD PTR [rsp-0x60],r10
lea    rax,[r9+r10*1]
mov    QWORD PTR [rsp-0x68],rax
xor    r15d,r15d
movdqa xmm1,XMMWORD PTR [RIP:DATA16:ffffff7f00000000ffffff7f00000000]
movdqa xmm2,XMMWORD PTR [RIP:DATA16:00000080000000000000008000000000]
movdqa xmm3,XMMWORD PTR [RIP:DATA16:feffffff00000000feffffff00000000]
pxor   xmm4,xmm4
movaps xmm5,XMMWORD PTR [RIP:DATA16:01000080010000800100008001000080]
movdqa xmm6,XMMWORD PTR [RIP:DATA16:00000080000000800000008000000080]
mov    QWORD PTR [rsp-0x38],r13
mov    QWORD PTR [rsp-0x40],r8
mov    QWORD PTR [rsp-0x30],rdi
mov    QWORD PTR [rsp-0x28],rsi
mov    QWORD PTR [rsp-0x18],rcx
mov    QWORD PTR [rsp-0x20],rdx
cs nop WORD PTR [rax+rax*1+0x0]
mov    r11d,r13d
mov    rax,QWORD PTR [rsp-0x20]
mov    edx,DWORD PTR [rax+r15*4]
mov    rax,rdx
mov    ecx,r8d
mov    r14d,edi
mov    r12,rdx
mov    rbx,rdx
mov    r9d,esi
imul   rdx,r9
imul   rax,r11
mov    QWORD PTR [rsp-0x8],rax
mov    rax,r11
imul   rax,QWORD PTR [rsp-0x38]
mov    r10d,eax
and    r10d,0x7fffffff
shr    rax,0x1f
add    rax,r10
mov    r10d,eax
imul   r12,rcx
mov    QWORD PTR [rsp-0x10],r12
and    r10d,0x7fffffff
shr    rax,0x1f
add    rax,r10
imul   rbx,r14
lea    r10d,[rax-0x7fffffff]
cmp    rax,0x7fffffff
cmovb  r10d,eax
mov    rax,rcx
imul   rax,QWORD PTR [rsp-0x40]
mov    ebp,eax
and    ebp,0x7fffffff
shr    rax,0x1f
add    rax,rbp
mov    ebp,eax
and    ebp,0x7fffffff
shr    rax,0x1f
add    rax,rbp
mov    ebp,0x0
cmp    rax,0x7fffffff
mov    r12d,0x7fffffff
cmovae ebp,r12d
add    rcx,r11
imul   rcx,QWORD PTR [rsp-0x48]
mov    r11d,ecx
and    r11d,0x7fffffff
shr    rcx,0x1f
sub    ebp,eax
add    rcx,r11
mov    eax,ecx
shr    rcx,0x1f
and    eax,0x7fffffff
add    rcx,rax
lea    eax,[r10+rbp*1]
add    eax,0x7fffffff
lea    r11d,[rax-0x7fffffff]
cmp    eax,0x7fffffff
cmovb  r11d,eax
lea    eax,[rcx+0x7fffffff]
cmp    rcx,0x7fffffff
cmovae eax,ecx
sub    eax,r10d
lea    ecx,[rax+rbp*1]
add    ecx,0x7fffffff
lea    r10d,[rcx-0x7fffffff]
cmp    eax,0x7fffffff
cmovb  r10d,ecx
lea    eax,[r10-0x7fffffff]
cmp    r10d,0x7fffffff
cmovb  eax,r10d
mov    rcx,r14
imul   rcx,QWORD PTR [rsp-0x30]
mov    r10d,ecx
and    r10d,0x7fffffff
shr    rcx,0x1f
add    rcx,r10
mov    r10d,ecx
and    r10d,0x7fffffff
shr    rcx,0x1f
add    rcx,r10
lea    r10d,[rcx-0x7fffffff]
cmp    rcx,0x7fffffff
cmovb  r10d,ecx
mov    rcx,r9
imul   rcx,QWORD PTR [rsp-0x28]
mov    ebp,ecx
and    ebp,0x7fffffff
shr    rcx,0x1f
add    rcx,rbp
mov    ebp,ecx
and    ebp,0x7fffffff
shr    rcx,0x1f
add    rcx,rbp
cmp    rcx,0x7fffffff
mov    ebp,0x0
cmovae ebp,r12d
add    r9,r14
imul   r9,QWORD PTR [rsp-0x50]
mov    r14d,r9d
sub    ebp,ecx
and    r14d,0x7fffffff
shr    r9,0x1f
add    r9,r14
mov    ecx,r9d
and    ecx,0x7fffffff
shr    r9,0x1f
lea    r12d,[r10+rbp*1]
add    r12d,0x7fffffff
add    r9,rcx
lea    r14d,[r12-0x7fffffff]
cmp    r12d,0x7fffffff
cmovb  r14d,r12d
lea    ecx,[r9+0x7fffffff]
cmp    r9,0x7fffffff
cmovae ecx,r9d
sub    ecx,r10d
lea    r9d,[rcx+rbp*1]
add    r9d,0x7fffffff
cmp    ecx,0x7fffffff
lea    ecx,[r9-0x7fffffff]
cmovb  ecx,r9d
lea    r10d,[rdi+r13*1]
add    edi,r13d
add    edi,0x80000001
lea    r9d,[rcx-0x7fffffff]
cmp    ecx,0x7fffffff
cmovb  r9d,ecx
cmp    r10d,0x7fffffff
cmovb  edi,r10d
lea    ecx,[rsi+r8*1]
add    esi,r8d
add    esi,0x80000001
cmp    ecx,0x7fffffff
cmovb  esi,ecx
movq   xmm8,rdx
mov    rcx,rdi
imul   rcx,QWORD PTR [rsp-0x58]
mov    edx,ecx
and    edx,0x7fffffff
shr    rcx,0x1f
add    rcx,rdx
mov    edx,ecx
and    edx,0x7fffffff
shr    rcx,0x1f
add    rcx,rdx
movq   xmm7,rbx
lea    edx,[rcx-0x7fffffff]
cmp    rcx,0x7fffffff
cmovb  edx,ecx
movq   xmm10,QWORD PTR [rsp-0x10]
mov    r8,rsi
imul   r8,QWORD PTR [rsp-0x60]
mov    ecx,r8d
and    ecx,0x7fffffff
shr    r8,0x1f
add    r8,rcx
mov    ecx,r8d
and    ecx,0x7fffffff
shr    r8,0x1f
add    r8,rcx
movq   xmm9,QWORD PTR [rsp-0x8]
cmp    r8,0x7fffffff
mov    r10d,0x0
mov    ecx,0x7fffffff
cmovae r10d,ecx
add    rsi,rdi
imul   rsi,QWORD PTR [rsp-0x68]
mov    ecx,esi
and    ecx,0x7fffffff
shr    rsi,0x1f
add    rsi,rcx
mov    ecx,esi
sub    r10d,r8d
and    ecx,0x7fffffff
shr    rsi,0x1f
add    rsi,rcx
lea    edi,[rsi+0x7fffffff]
cmp    rsi,0x7fffffff
cmovae edi,esi
lea    ecx,[r10+rdx*1]
add    ecx,0x7fffffff
sub    edi,edx
lea    esi,[rdi+r10*1]
add    esi,0x7fffffff
cmp    edi,0x7fffffff
lea    edx,[rsi-0x7fffffff]
cmovb  edx,esi
lea    esi,[r14+r14*1]
cmp    esi,0x7fffffff
lea    edi,[r14+r14*1+0x7fffffff]
cmovae edi,esi
sub    edi,r9d
lea    esi,[r9+r9*1]
cmp    esi,0x7fffffff
lea    esi,[r14+r9*2]
lea    r8d,[r14+r9*2-0x7fffffff]
cmovb  r8d,esi
lea    esi,[rdi+r11*1]
cmp    edi,0x7fffffff
lea    edi,[rdi+r11*1-0x7fffffff]
cmovb  edi,esi
lea    r13d,[rdi-0x7fffffff]
cmp    edi,0x7fffffff
cmovb  r13d,edi
lea    esi,[r8+rax*1]
cmp    r8d,0x7fffffff
lea    edi,[r8+rax*1-0x7fffffff]
cmovb  edi,esi
lea    r8d,[rdi-0x7fffffff]
cmp    edi,0x7fffffff
cmovb  r8d,edi
mov    esi,ecx
sub    esi,r11d
cmp    ecx,0x7fffffff
lea    ecx,[rsi+0x7fffffff]
cmovae ecx,esi
mov    esi,edx
sub    esi,eax
cmp    edx,0x7fffffff
lea    eax,[rsi+0x7fffffff]
cmovae eax,esi
mov    edx,ecx
sub    edx,r14d
cmp    ecx,0x7fffffff
lea    ecx,[rdx+0x7fffffff]
cmovae ecx,edx
lea    edi,[rcx-0x7fffffff]
cmp    ecx,0x7fffffff
cmovb  edi,ecx
mov    ecx,eax
sub    ecx,r9d
cmp    eax,0x7fffffff
lea    eax,[rcx+0x7fffffff]
cmovae eax,ecx
mov    rcx,QWORD PTR [rsp-0x18]
lea    esi,[rax-0x7fffffff]
cmp    eax,0x7fffffff
cmovb  esi,eax
punpcklqdq xmm7,xmm8
punpcklqdq xmm9,xmm10
movdqa xmm8,xmm9
pand   xmm8,xmm1
movdqa xmm10,xmm7
pand   xmm10,xmm1
psrlq  xmm9,0x1f
paddq  xmm9,xmm8
psrlq  xmm7,0x1f
paddq  xmm7,xmm10
movdqa xmm8,xmm9
pand   xmm8,xmm1
movdqa xmm10,xmm7
pand   xmm10,xmm1
psrlq  xmm9,0x1f
paddq  xmm9,xmm8
psrlq  xmm7,0x1f
paddq  xmm7,xmm10
movdqa xmm8,xmm9
shufps xmm8,xmm7,0x88
pxor   xmm7,xmm2
pxor   xmm9,xmm2
movdqa xmm10,xmm9
paddd  xmm8,xmm0
shufps xmm9,xmm7,0xdd
pcmpgtd xmm10,xmm3
pcmpgtd xmm7,xmm3
movdqa xmm0,xmm10
shufps xmm0,xmm7,0x88
pcmpeqd xmm9,xmm4
pand   xmm9,xmm0
shufps xmm10,xmm7,0xdd
orps   xmm10,xmm9
andps  xmm10,xmm5
paddd  xmm10,xmm8
movdqa xmm7,xmm10
pxor   xmm7,xmm6
pcmpeqd xmm0,xmm0
pcmpgtd xmm0,xmm7
pandn  xmm0,xmm5
paddd  xmm0,xmm10
inc    r15
cmp    rcx,r15
jne    LOCAL+0xd0
mov    rax,QWORD PTR [rsp-0x70]
movdqu XMMWORD PTR [rax],xmm0
pop    rbx
pop    r12
pop    r13
pop    r14
pop    r15
pop    rbp
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
int3
