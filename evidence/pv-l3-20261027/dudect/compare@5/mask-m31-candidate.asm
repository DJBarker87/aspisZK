aspis_prover::state_only_hiding::sample_mask_cells @ 0x13bee0
push   rbp
push   r15
push   r14
push   r13
push   r12
push   rbx
sub    rsp,0xc8
movabs rcx,0x7ffffffffffffffc
lea    r12,[rdx*4+0x0]
mov    rax,rdx
shr    rax,0x3e
setne  al
cmp    r12,rcx
seta   cl
or     cl,al
je     LOCAL+0x46
xor    r13d,r13d
mov    rdi,r13
mov    rsi,r12
call   QWORD PTR [RIP:alloc::raw_vec::handle_error]
mov    r15,rsi
test   r12,r12
mov    QWORD PTR [rsp+0x20],rdi
je     LOCAL+0x7d
mov    rbx,rdx
call   QWORD PTR [RIP:__rustc::__rust_no_alloc_shim_is_unstable_v2]
mov    r13d,0x4
mov    esi,0x4
mov    rdi,r12
call   QWORD PTR [RIP:__rustc::__rust_alloc]
test   rax,rax
je     LOCAL+0x3a
mov    rdx,rbx
mov    rcx,rbx
jmp    LOCAL+0x84
mov    eax,0x4
xor    ecx,ecx
mov    QWORD PTR [rsp+0x8],rcx
mov    QWORD PTR [rsp+0x10],rax
mov    QWORD PTR [rsp+0x18],0x0
test   rdx,rdx
je     LOCAL+0x20e
mov    rax,QWORD PTR [r15]
mov    QWORD PTR [rsp+0x40],rax
mov    rbp,QWORD PTR [r15+0x28]
lea    rax,[r15+0x8]
mov    QWORD PTR [rsp+0x38],rax
lea    r13,[r15+0x30]
mov    rbx,QWORD PTR [r15+0x50]
xor    eax,eax
mov    QWORD PTR [rsp+0x28],rdx
mov    QWORD PTR [rsp+0x30],rax
mov    r14d,0x10
nop
cmp    rbx,0x8
jne    LOCAL+0x190
mov    rax,QWORD PTR [rsp+0x38]
movups xmm0,XMMWORD PTR [rax]
movups xmm1,XMMWORD PTR [rax+0x10]
movaps XMMWORD PTR [rsp+0x90],xmm1
movaps XMMWORD PTR [rsp+0x80],xmm0
mov    QWORD PTR [rsp+0x48],rbp
lea    rax,[RIP:anon.93b5e49d352837b62369596380fc4a46.41.llvm.8837383725297823176+0x40]
mov    QWORD PTR [rsp+0x50],rax
mov    QWORD PTR [rsp+0x58],0x27
lea    rax,[rsp+0x80]
mov    QWORD PTR [rsp+0x60],rax
mov    QWORD PTR [rsp+0x68],0x20
lea    rax,[rsp+0x48]
mov    QWORD PTR [rsp+0x70],rax
mov    QWORD PTR [rsp+0x78],0x8
mov    edx,0x3
lea    rdi,[rsp+0xa8]
lea    rsi,[rsp+0x50]
call   QWORD PTR [rsp+0x40]
movups xmm0,XMMWORD PTR [rsp+0xa8]
movups xmm1,XMMWORD PTR [rsp+0xb8]
movups XMMWORD PTR [r13+0x10],xmm1
movups XMMWORD PTR [r13+0x0],xmm0
inc    rbp
mov    QWORD PTR [r15+0x28],rbp
mov    QWORD PTR [r15+0x50],0x1
mov    ebx,0x1
xor    edi,edi
jmp    LOCAL+0x1a9
data16 data16 data16 data16 data16 cs nop WORD PTR [rax+rax*1+0x0]
lea    rdi,[rbx*4+0x0]
inc    rbx
mov    QWORD PTR [r15+0x50],rbx
cmp    rdi,0x20
jae    LOCAL+0x27c
mov    r12d,DWORD PTR [r13+rdi*1+0x0]
mov    eax,0x7fffffff
and    r12d,eax
cmp    r12d,0x7fffffff
jne    LOCAL+0x1d0
dec    r14
jne    LOCAL+0xd0
jmp    LOCAL+0x22f
nop    WORD PTR [rax+rax*1+0x0]
mov    r14,QWORD PTR [rsp+0x18]
cmp    r14,QWORD PTR [rsp+0x8]
jne    LOCAL+0x1e7
lea    rdi,[rsp+0x8]
call   QWORD PTR [RIP:_DYNAMIC+0x978]
mov    rax,QWORD PTR [rsp+0x10]
mov    DWORD PTR [rax+r14*4],r12d
inc    r14
mov    QWORD PTR [rsp+0x18],r14
mov    rax,QWORD PTR [rsp+0x30]
inc    rax
mov    rdx,QWORD PTR [rsp+0x28]
cmp    rax,rdx
jne    LOCAL+0xc4
mov    rax,QWORD PTR [rsp+0x18]
mov    rbx,QWORD PTR [rsp+0x20]
mov    QWORD PTR [rbx+0x10],rax
mov    rax,QWORD PTR [rsp+0x8]
mov    QWORD PTR [rbx],rax
mov    rax,QWORD PTR [rsp+0x10]
mov    QWORD PTR [rbx+0x8],rax
jmp    LOCAL+0x267
mov    rbx,QWORD PTR [rsp+0x20]
mov    BYTE PTR [rbx+0x8],0x2
movabs rax,0x7ffffffffffffffc
add    rax,0x4
mov    QWORD PTR [rbx],rax
mov    rsi,QWORD PTR [rsp+0x8]
test   rsi,rsi
je     LOCAL+0x267
mov    rdi,QWORD PTR [rsp+0x10]
shl    rsi,0x2
mov    edx,0x4
call   QWORD PTR [RIP:__rustc::__rust_dealloc]
mov    rax,rbx
add    rsp,0xc8
pop    rbx
pop    r12
pop    r13
pop    r14
pop    r15
pop    rbp
ret
lea    rsi,[rdi+0x4]
lea    rcx,[RIP:anon.144c014deabc1ff788eba05e4c9de081.5.llvm.18047182005676867147+0x18]
mov    edx,0x20
call   QWORD PTR [RIP:core::slice::index::slice_index_fail]
ud2
jmp    LOCAL+0x298
jmp    LOCAL+0x298
mov    rbx,rax
mov    rsi,QWORD PTR [rsp+0x8]
test   rsi,rsi
je     LOCAL+0x2b9
mov    rdi,QWORD PTR [rsp+0x10]
shl    rsi,0x2
mov    edx,0x4
call   QWORD PTR [RIP:__rustc::__rust_dealloc]
mov    rdi,rbx
call   _Unwind_Resume@plt
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
