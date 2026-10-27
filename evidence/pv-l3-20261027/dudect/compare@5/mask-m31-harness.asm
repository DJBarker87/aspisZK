pv_dudect::kernels::state_only_hiding::measure_m31 @ 0x37700
push   rbp
push   r15
push   r14
push   r13
push   r12
push   rbx
sub    rsp,0x88
mov    rbx,rdi
mov    rcx,QWORD PTR [rdi+0x50]
mov    r12,QWORD PTR [rdi]
mov    r13,QWORD PTR [rdi+0x28]
lea    rbp,[rdi+0x8]
lea    r14,[rdi+0x30]
mov    r15d,0x10
nop    DWORD PTR [rax]
cmp    rcx,0x8
je     LOCAL+0x70
lea    rdi,[rcx*4+0x0]
inc    rcx
mov    QWORD PTR [rbx+0x50],rcx
cmp    rdi,0x20
jae    LOCAL+0x13a
mov    eax,DWORD PTR [r14+rdi*1]
and    eax,0x7fffffff
cmp    rax,0x7fffffff
je     LOCAL+0x10e
jmp    LOCAL+0x11e
nop    DWORD PTR [rax+0x0]
movups xmm0,XMMWORD PTR [rbp+0x0]
movups xmm1,XMMWORD PTR [rbp+0x10]
movaps XMMWORD PTR [rsp+0x50],xmm1
movaps XMMWORD PTR [rsp+0x40],xmm0
mov    QWORD PTR [rsp+0x8],r13
lea    rax,[RIP:anon.cc9e1b464619ab62d021e6446458583c.0.llvm.15800808401943094617+0x1c]
mov    QWORD PTR [rsp+0x10],rax
mov    QWORD PTR [rsp+0x18],0x27
lea    rax,[rsp+0x40]
mov    QWORD PTR [rsp+0x20],rax
mov    QWORD PTR [rsp+0x28],0x20
lea    rax,[rsp+0x8]
mov    QWORD PTR [rsp+0x30],rax
mov    QWORD PTR [rsp+0x38],0x8
mov    edx,0x3
lea    rdi,[rsp+0x68]
lea    rsi,[rsp+0x10]
call   r12
movups xmm0,XMMWORD PTR [rsp+0x68]
movups xmm1,XMMWORD PTR [rsp+0x78]
movups XMMWORD PTR [r14+0x10],xmm1
movups XMMWORD PTR [r14],xmm0
inc    r13
mov    QWORD PTR [rbx+0x28],r13
mov    QWORD PTR [rbx+0x50],0x1
mov    ecx,0x1
xor    edi,edi
mov    eax,DWORD PTR [r14+rdi*1]
and    eax,0x7fffffff
cmp    rax,0x7fffffff
jne    LOCAL+0x11e
dec    r15
jne    LOCAL+0x30
mov    eax,0x201
jmp    LOCAL+0x128
shl    rax,0x20
or     rax,0x200
add    rsp,0x88
pop    rbx
pop    r12
pop    r13
pop    r14
pop    r15
pop    rbp
ret
lea    rsi,[rdi+0x4]
lea    rcx,[RIP:anon.cc9e1b464619ab62d021e6446458583c.4.llvm.15800808401943094617+0x30]
mov    edx,0x20
call   QWORD PTR [RIP:core::slice::index::slice_index_fail]
