aspis_prover::state_only_hiding::SeedExpander::qm31 @ 0x13b900
push   rbp
push   r15
push   r14
push   r13
push   r12
push   rbx
sub    rsp,0x98
mov    r14,rsi
mov    QWORD PTR [rsp+0x8],rdi
mov    rax,QWORD PTR [rsi+0x50]
mov    rcx,QWORD PTR [rsi]
mov    QWORD PTR [rsp+0x18],rcx
mov    rdx,QWORD PTR [rsi+0x28]
lea    rcx,[rsi+0x8]
mov    QWORD PTR [rsp+0x10],rcx
lea    r15,[rsi+0x30]
mov    ebx,0x10
lea    r12,[rsp+0x20]
mov    ebp,0x7fffffff
data16 cs nop WORD PTR [rax+rax*1+0x0]
cmp    rax,0x8
je     LOCAL+0x90
lea    rdi,[rax*4+0x0]
inc    rax
mov    QWORD PTR [r14+0x50],rax
cmp    rdi,0x20
jae    LOCAL+0x494
mov    r13d,DWORD PTR [r15+rdi*1]
and    r13d,ebp
cmp    r13d,0x7fffffff
je     LOCAL+0x136
jmp    LOCAL+0x144
nop    DWORD PTR [rax+rax*1+0x0]
mov    rax,QWORD PTR [rsp+0x10]
movups xmm0,XMMWORD PTR [rax]
movups xmm1,XMMWORD PTR [rax+0x10]
movaps XMMWORD PTR [rsp+0x60],xmm1
movaps XMMWORD PTR [rsp+0x50],xmm0
mov    QWORD PTR [rsp],rdx
lea    rax,[RIP:anon.93b5e49d352837b62369596380fc4a46.41.llvm.4117853321344695235+0x40]
mov    QWORD PTR [rsp+0x20],rax
mov    QWORD PTR [rsp+0x28],0x27
lea    rax,[rsp+0x50]
mov    QWORD PTR [rsp+0x30],rax
mov    QWORD PTR [rsp+0x38],0x20
mov    rax,rsp
mov    QWORD PTR [rsp+0x40],rax
mov    QWORD PTR [rsp+0x48],0x8
mov    r13,rdx
mov    edx,0x3
lea    rdi,[rsp+0x70]
mov    rsi,r12
call   QWORD PTR [rsp+0x18]
mov    rdx,r13
movups xmm0,XMMWORD PTR [rsp+0x70]
movups xmm1,XMMWORD PTR [rsp+0x80]
movups XMMWORD PTR [r15+0x10],xmm1
movups XMMWORD PTR [r15],xmm0
inc    rdx
mov    QWORD PTR [r14+0x28],rdx
mov    QWORD PTR [r14+0x50],0x1
mov    eax,0x1
xor    edi,edi
mov    r13d,DWORD PTR [r15+rdi*1]
and    r13d,ebp
cmp    r13d,0x7fffffff
jne    LOCAL+0x144
dec    rbx
jne    LOCAL+0x50
jmp    LOCAL+0x45e
mov    ebx,0x10
mov    ebp,0x7fffffff
xchg   ax,ax
cmp    rax,0x8
je     LOCAL+0x190
lea    rdi,[rax*4+0x0]
inc    rax
mov    QWORD PTR [r14+0x50],rax
cmp    rdi,0x20
jae    LOCAL+0x494
mov    r12d,DWORD PTR [r15+rdi*1]
and    r12d,ebp
cmp    r12d,0x7fffffff
je     LOCAL+0x238
jmp    LOCAL+0x246
nop    DWORD PTR [rax+rax*1+0x0]
mov    rax,QWORD PTR [rsp+0x10]
movups xmm0,XMMWORD PTR [rax]
movups xmm1,XMMWORD PTR [rax+0x10]
movaps XMMWORD PTR [rsp+0x60],xmm1
movaps XMMWORD PTR [rsp+0x50],xmm0
mov    QWORD PTR [rsp],rdx
lea    rax,[RIP:anon.93b5e49d352837b62369596380fc4a46.41.llvm.4117853321344695235+0x40]
mov    QWORD PTR [rsp+0x20],rax
mov    QWORD PTR [rsp+0x28],0x27
lea    rax,[rsp+0x50]
mov    QWORD PTR [rsp+0x30],rax
mov    QWORD PTR [rsp+0x38],0x20
mov    rax,rsp
mov    QWORD PTR [rsp+0x40],rax
mov    QWORD PTR [rsp+0x48],0x8
mov    r12,rdx
mov    edx,0x3
lea    rdi,[rsp+0x70]
lea    rsi,[rsp+0x20]
call   QWORD PTR [rsp+0x18]
mov    rdx,r12
movups xmm0,XMMWORD PTR [rsp+0x70]
movups xmm1,XMMWORD PTR [rsp+0x80]
movups XMMWORD PTR [r15+0x10],xmm1
movups XMMWORD PTR [r15],xmm0
inc    rdx
mov    QWORD PTR [r14+0x28],rdx
mov    QWORD PTR [r14+0x50],0x1
mov    eax,0x1
xor    edi,edi
mov    r12d,DWORD PTR [r15+rdi*1]
and    r12d,ebp
cmp    r12d,0x7fffffff
jne    LOCAL+0x246
dec    rbx
jne    LOCAL+0x150
jmp    LOCAL+0x45e
mov    ebp,0x10
mov    ecx,0x7fffffff
cmp    rax,0x8
je     LOCAL+0x290
lea    rdi,[rax*4+0x0]
inc    rax
mov    QWORD PTR [r14+0x50],rax
cmp    rdi,0x20
jae    LOCAL+0x494
mov    ebx,DWORD PTR [r15+rdi*1]
and    ebx,ecx
cmp    ebx,0x7fffffff
je     LOCAL+0x33b
jmp    LOCAL+0x349
cs nop WORD PTR [rax+rax*1+0x0]
mov    rax,QWORD PTR [rsp+0x10]
movups xmm0,XMMWORD PTR [rax]
movups xmm1,XMMWORD PTR [rax+0x10]
movaps XMMWORD PTR [rsp+0x60],xmm1
movaps XMMWORD PTR [rsp+0x50],xmm0
mov    QWORD PTR [rsp],rdx
lea    rax,[RIP:anon.93b5e49d352837b62369596380fc4a46.41.llvm.4117853321344695235+0x40]
mov    QWORD PTR [rsp+0x20],rax
mov    QWORD PTR [rsp+0x28],0x27
lea    rax,[rsp+0x50]
mov    QWORD PTR [rsp+0x30],rax
mov    QWORD PTR [rsp+0x38],0x20
mov    rax,rsp
mov    QWORD PTR [rsp+0x40],rax
mov    QWORD PTR [rsp+0x48],0x8
mov    rbx,rdx
mov    edx,0x3
lea    rdi,[rsp+0x70]
lea    rsi,[rsp+0x20]
call   QWORD PTR [rsp+0x18]
mov    ecx,0x7fffffff
mov    rdx,rbx
movups xmm0,XMMWORD PTR [rsp+0x70]
movups xmm1,XMMWORD PTR [rsp+0x80]
movups XMMWORD PTR [r15+0x10],xmm1
movups XMMWORD PTR [r15],xmm0
inc    rdx
mov    QWORD PTR [r14+0x28],rdx
mov    QWORD PTR [r14+0x50],0x1
mov    eax,0x1
xor    edi,edi
mov    ebx,DWORD PTR [r15+rdi*1]
and    ebx,ecx
cmp    ebx,0x7fffffff
jne    LOCAL+0x349
dec    rbp
jne    LOCAL+0x250
jmp    LOCAL+0x45e
mov    ebp,0x10
mov    esi,0x7fffffff
data16 data16 data16 cs nop WORD PTR [rax+rax*1+0x0]
cmp    rax,0x8
je     LOCAL+0x3a0
lea    rdi,[rax*4+0x0]
inc    rax
mov    QWORD PTR [r14+0x50],rax
cmp    rdi,0x20
jae    LOCAL+0x494
mov    ecx,DWORD PTR [r15+rdi*1]
and    ecx,esi
cmp    ecx,0x7fffffff
je     LOCAL+0x455
jmp    LOCAL+0x47d
cs nop WORD PTR [rax+rax*1+0x0]
mov    rax,QWORD PTR [rsp+0x10]
movups xmm0,XMMWORD PTR [rax]
movups xmm1,XMMWORD PTR [rax+0x10]
movaps XMMWORD PTR [rsp+0x60],xmm1
movaps XMMWORD PTR [rsp+0x50],xmm0
mov    QWORD PTR [rsp],rdx
lea    rax,[RIP:anon.93b5e49d352837b62369596380fc4a46.41.llvm.4117853321344695235+0x40]
mov    QWORD PTR [rsp+0x20],rax
mov    QWORD PTR [rsp+0x28],0x27
lea    rax,[rsp+0x50]
mov    QWORD PTR [rsp+0x30],rax
mov    QWORD PTR [rsp+0x38],0x20
mov    rax,rsp
mov    QWORD PTR [rsp+0x40],rax
mov    QWORD PTR [rsp+0x48],0x8
mov    QWORD PTR [rsp+0x90],rdx
mov    edx,0x3
lea    rdi,[rsp+0x70]
lea    rsi,[rsp+0x20]
call   QWORD PTR [rsp+0x18]
mov    esi,0x7fffffff
mov    rdx,QWORD PTR [rsp+0x90]
movups xmm0,XMMWORD PTR [rsp+0x70]
movups xmm1,XMMWORD PTR [rsp+0x80]
movups XMMWORD PTR [r15+0x10],xmm1
movups XMMWORD PTR [r15],xmm0
inc    rdx
mov    QWORD PTR [r14+0x28],rdx
mov    QWORD PTR [r14+0x50],0x1
mov    eax,0x1
xor    edi,edi
mov    ecx,DWORD PTR [r15+rdi*1]
and    ecx,esi
cmp    ecx,0x7fffffff
jne    LOCAL+0x47d
dec    rbp
jne    LOCAL+0x360
mov    rdx,QWORD PTR [rsp+0x8]
mov    BYTE PTR [rdx+0x1],0x2
mov    al,0x1
mov    BYTE PTR [rdx],al
add    rsp,0x98
pop    rbx
pop    r12
pop    r13
pop    r14
pop    r15
pop    rbp
ret
mov    rdx,QWORD PTR [rsp+0x8]
mov    DWORD PTR [rdx+0x4],r13d
mov    DWORD PTR [rdx+0x8],r12d
mov    DWORD PTR [rdx+0xc],ebx
mov    DWORD PTR [rdx+0x10],ecx
xor    eax,eax
jmp    LOCAL+0x469
lea    rsi,[rdi+0x4]
lea    rcx,[RIP:anon.144c014deabc1ff788eba05e4c9de081.5.llvm.10553217263700975778+0x18]
mov    edx,0x20
call   QWORD PTR [RIP:core::slice::index::slice_index_fail]
int3
int3
int3
int3
int3
int3
