pv_dudect::inverse_q @ 0x33470
jmp    QWORD PTR [RIP:aspis_core::field::QM31::inv]
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

aspis_core::field::QM31::inv @ 0x43570
push   rbx
sub    rsp,0x20
mov    rbx,rdi
lea    rdi,[rsp+0xc]
call   QWORD PTR [RIP:aspis_core::field::QM31::try_inv]
cmp    DWORD PTR [rsp+0xc],0x1
jne    LOCAL+0x2b
movups xmm0,XMMWORD PTR [rsp+0x10]
movups XMMWORD PTR [rbx],xmm0
mov    rax,rbx
add    rsp,0x20
pop    rbx
ret
lea    rdi,[RIP:anon.4542838882158fab56838ae26b7212f7.176.llvm.13126917640099348842+0x8f]
lea    rdx,[RIP:anon.d5090c25a416dcf11afff7dd91233e4e.8.llvm.13100340739265517091+0x48]
mov    esi,0x1a
call   QWORD PTR [RIP:core::option::expect_failed]
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

aspis_core::field::QM31::try_inv @ 0x435c0
push   rbp
push   r15
push   r14
push   r13
push   r12
push   rbx
sub    rsp,0x18
mov    rax,rdi
mov    ebp,DWORD PTR [rsi]
mov    r13d,DWORD PTR [rsi+0x4]
mov    r15d,DWORD PTR [rsi+0x8]
mov    esi,DWORD PTR [rsi+0xc]
mov    ecx,r13d
or     ecx,ebp
or     ecx,r15d
or     ecx,esi
je     LOCAL+0x4d7
mov    r12,r13
add    r12,rbp
mov    r9,rbp
sub    r9,r13
add    r9,0x7fffffff
imul   r9,r12
mov    QWORD PTR [rsp+0x10],rax
mov    ecx,r9d
and    ecx,0x7fffffff
shr    r9,0x1f
add    r9,rcx
mov    ecx,r9d
and    ecx,0x7fffffff
shr    r9,0x1f
add    r9,rcx
mov    rcx,r13
imul   rcx,rbp
mov    edx,ecx
and    edx,0x7fffffff
shr    rcx,0x1f
add    rcx,rdx
mov    edx,ecx
and    edx,0x7fffffff
shr    rcx,0x1f
add    rcx,rdx
cmp    rcx,0x7fffffff
sbb    ecx,0xffffffff
lea    rdx,[rsi+r15*1]
mov    rax,rsi
mov    rsi,r15
sub    rsi,rax
mov    QWORD PTR [rsp+0x8],rax
add    rsi,0x7fffffff
imul   rsi,rdx
mov    edx,esi
and    edx,0x7fffffff
shr    rsi,0x1f
add    rsi,rdx
mov    edx,esi
and    edx,0x7fffffff
shr    rsi,0x1f
add    rsi,rdx
lea    edx,[rsi-0x7fffffff]
cmp    rsi,0x7fffffff
cmovb  edx,esi
mov    rsi,rax
imul   rsi,r15
mov    edi,esi
and    edi,0x7fffffff
shr    rsi,0x1f
add    rsi,rdi
mov    edi,esi
and    edi,0x7fffffff
shr    rsi,0x1f
add    rsi,rdi
cmp    rsi,0x7fffffff
sbb    esi,0xffffffff
lea    edi,[rsi+rsi*1]
cmp    edi,0x7fffffff
lea    esi,[rsi+rsi*1-0x7fffffff]
cmovb  esi,edi
lea    edi,[rdx+rdx*1]
cmp    edi,0x7fffffff
lea    r8d,[rdx+rdx*1+0x7fffffff]
cmovae r8d,edi
sub    r8d,esi
lea    edi,[rsi+rsi*1]
cmp    edi,0x7fffffff
lea    edi,[rdx+rsi*2]
lea    edx,[rdx+rsi*2-0x7fffffff]
cmovb  edx,edi
lea    esi,[r9+0x7fffffff]
cmp    r9,0x7fffffff
cmovae esi,r9d
lea    eax,[rcx+rcx*1]
sub    esi,r8d
lea    edi,[rsi+0x7fffffff]
cmp    r8d,0x7fffffff
cmovb  edi,esi
lea    ebx,[rdi-0x7fffffff]
cmp    edi,0x7fffffff
cmovb  ebx,edi
cmp    eax,0x7fffffff
lea    ecx,[rcx+rcx*1+0x7fffffff]
cmovae ecx,eax
sub    ecx,edx
lea    eax,[rcx+0x7fffffff]
cmp    edx,0x7fffffff
cmovb  eax,ecx
lea    r14d,[rax-0x7fffffff]
cmp    eax,0x7fffffff
cmovb  r14d,eax
mov    rax,rbx
imul   rax,rbx
mov    ecx,eax
and    ecx,0x7ffffffd
shr    rax,0x1f
add    rax,rcx
mov    ecx,eax
and    ecx,0x7fffffff
shr    rax,0x1f
add    rax,rcx
mov    rcx,r14
imul   rcx,r14
mov    edx,ecx
and    edx,0x7ffffffd
shr    rcx,0x1f
add    rcx,rdx
mov    edx,ecx
and    edx,0x7fffffff
shr    rcx,0x1f
add    rcx,rdx
lea    edx,[rax-0x7fffffff]
cmp    rax,0x7fffffff
cmovb  edx,eax
lea    eax,[rdx+rcx*1]
cmp    rcx,0x7fffffff
lea    ecx,[rdx+rcx*1-0x7fffffff]
cmovb  ecx,eax
lea    edi,[rcx-0x7fffffff]
cmp    ecx,0x7fffffff
cmovb  edi,ecx
call   QWORD PTR [RIP:aspis_core::field::M31::inv]
mov    edx,eax
imul   rbx,rdx
mov    eax,ebx
and    eax,0x7fffffff
shr    rbx,0x1f
add    rbx,rax
mov    eax,ebx
and    eax,0x7fffffff
shr    rbx,0x1f
add    rbx,rax
xor    eax,eax
cmp    rbx,0x7fffffff
mov    esi,0x80000001
mov    ecx,0x0
cmovae ecx,esi
add    ebx,ecx
mov    ecx,r14d
xor    ecx,0x7fffffff
test   r14d,r14d
cmove  ecx,r14d
imul   rcx,rdx
mov    edx,ecx
and    edx,0x7fffffff
shr    rcx,0x1f
add    rcx,rdx
mov    edx,ecx
and    edx,0x7fffffff
shr    rcx,0x1f
add    rcx,rdx
cmp    rcx,0x7fffffff
cmovb  esi,eax
add    ecx,esi
imul   rbp,rbx
mov    edx,ebp
and    edx,0x7fffffff
shr    rbp,0x1f
add    rbp,rdx
mov    edx,ebp
and    edx,0x7fffffff
shr    rbp,0x1f
add    rbp,rdx
lea    esi,[rbp-0x7fffffff]
cmp    rbp,0x7fffffff
cmovb  esi,ebp
imul   r13,rcx
mov    edx,r13d
and    edx,0x7fffffff
shr    r13,0x1f
add    r13,rdx
mov    edx,r13d
and    edx,0x7fffffff
shr    r13,0x1f
add    r13,rdx
cmp    r13,0x7fffffff
mov    r8d,0x7fffffff
mov    r9d,0x0
cmovae r9d,r8d
sub    r9d,r13d
lea    rdi,[rbx+rcx*1]
imul   r12,rdi
mov    edx,r12d
and    edx,0x7fffffff
shr    r12,0x1f
add    r12,rdx
mov    edx,r12d
and    edx,0x7fffffff
shr    r12,0x1f
add    r12,rdx
lea    r10d,[r9+rsi*1]
add    r10d,0x7fffffff
lea    edx,[r10-0x7fffffff]
cmp    r10d,0x7fffffff
cmovb  edx,r10d
lea    r10d,[r12+0x7fffffff]
cmp    r12,0x7fffffff
cmovae r10d,r12d
sub    r10d,esi
lea    esi,[r9+r10*1]
add    esi,0x7fffffff
lea    r9d,[rsi-0x7fffffff]
cmp    r10d,0x7fffffff
cmovb  r9d,esi
lea    esi,[r9-0x7fffffff]
cmp    r9d,0x7fffffff
cmovb  esi,r9d
mov    r11d,r15d
xor    r11d,0x7fffffff
test   r15,r15
cmove  r11d,eax
mov    r10,QWORD PTR [rsp+0x8]
mov    r9d,r10d
xor    r9d,0x7fffffff
test   r10,r10
cmove  r9d,eax
imul   rbx,r11
mov    r10d,ebx
and    r10d,0x7fffffff
shr    rbx,0x1f
add    rbx,r10
mov    r10d,ebx
and    r10d,0x7fffffff
shr    rbx,0x1f
add    rbx,r10
lea    r10d,[rbx-0x7fffffff]
cmp    rbx,0x7fffffff
cmovb  r10d,ebx
imul   rcx,r9
mov    ebx,ecx
and    ebx,0x7fffffff
shr    rcx,0x1f
add    rcx,rbx
mov    ebx,ecx
and    ebx,0x7fffffff
shr    rcx,0x1f
add    rcx,rbx
cmp    rcx,0x7fffffff
cmovae eax,r8d
sub    eax,ecx
add    r9,r11
imul   r9,rdi
mov    ecx,r9d
and    ecx,0x7fffffff
shr    r9,0x1f
add    r9,rcx
mov    ecx,r9d
and    ecx,0x7fffffff
shr    r9,0x1f
add    r9,rcx
lea    ecx,[rax+r10*1]
add    ecx,0x7fffffff
lea    edi,[rcx-0x7fffffff]
cmp    ecx,0x7fffffff
cmovb  edi,ecx
lea    ecx,[r9+0x7fffffff]
cmp    r9,0x7fffffff
cmovae ecx,r9d
sub    ecx,r10d
lea    r9d,[rax+rcx*1]
add    r9d,0x7fffffff
lea    r8d,[r9-0x7fffffff]
cmp    ecx,0x7fffffff
mov    rax,QWORD PTR [rsp+0x10]
cmovb  r8d,r9d
lea    ecx,[r8-0x7fffffff]
cmp    r8d,0x7fffffff
cmovb  ecx,r8d
mov    DWORD PTR [rax+0x4],edx
mov    DWORD PTR [rax+0x8],esi
mov    DWORD PTR [rax+0xc],edi
mov    DWORD PTR [rax+0x10],ecx
mov    ecx,0x1
jmp    LOCAL+0x4d9
xor    ecx,ecx
mov    DWORD PTR [rax],ecx
add    rsp,0x18
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
