aspis_r1_cost_probe::host_semantic::copy_endpoint_values @ 0xbc750
push   rbp
push   r15
push   r14
push   r13
push   r12
push   rbx
sub    rsp,0xf8
mov    r13,QWORD PTR [rsp+0x138]
mov    r12,QWORD PTR [rsp+0x130]
movzx  ebx,WORD PTR [rdx+0xc0]
cmp    rbx,0x3ff
ja     LOCAL+0x51
mov    rax,QWORD PTR [r13+0x10]
cmp    rax,rbx
jbe    LOCAL+0x8f7
mov    eax,ebx
shl    eax,0x4
add    rax,QWORD PTR [r13+0x8]
mov    r14,QWORD PTR [rax+r9*8]
cmp    r14,0x1
jbe    LOCAL+0x5a
mov    BYTE PTR [rdi+0x8],0xa
jmp    LOCAL+0x826
lea    r10,[r14+0x1]
mov    QWORD PTR [rax+r9*8],r10
xor    r15d,r15d
cmp    BYTE PTR [rdx],0x1
mov    eax,0x0
jne    LOCAL+0xf3
movzx  r11d,WORD PTR [rdx+0x2]
movzx  r15d,BYTE PTR [rdx+0x4]
mov    r10d,DWORD PTR [rdx+0x8]
cmp    BYTE PTR [rdx+0x6],0x0
je     LOCAL+0xae
mov    al,0xa
cmp    r15b,0xf
ja     LOCAL+0x445
lea    rbp,[r15+r15*2]
cmp    QWORD PTR [rsi+rbp*8+0x190],r11
jbe    LOCAL+0x445
lea    rbp,[rsi+0x180]
jmp    LOCAL+0xcc
mov    al,0xa
cmp    r15b,0xf
ja     LOCAL+0x445
lea    rax,[r15+r15*2]
mov    rbp,rsi
cmp    QWORD PTR [rsi+rax*8+0x10],r11
jbe    LOCAL+0x808
lea    rax,[r15+r15*2]
mov    rax,QWORD PTR [rbp+rax*8+0x8]
mov    eax,DWORD PTR [rax+r11*4]
lea    r11d,[rax+r10*1]
cmp    r11d,0x7fffffff
lea    eax,[rax+r10*1-0x7fffffff]
cmovb  eax,r11d
xor    r15d,r15d
test   BYTE PTR [rdx+0xc],0x1
mov    DWORD PTR [rsp+0x7c],eax
je     LOCAL+0x192
movzx  r11d,WORD PTR [rdx+0xe]
movzx  ebp,BYTE PTR [rdx+0x10]
mov    r10d,DWORD PTR [rdx+0x14]
test   BYTE PTR [rdx+0x12],0x1
je     LOCAL+0x142
mov    al,0xa
cmp    bpl,0xf
ja     LOCAL+0x445
lea    rax,[rbp*2+0x0]
add    rax,rbp
cmp    QWORD PTR [rsi+rax*8+0x190],r11
jbe    LOCAL+0x808
lea    r15,[rsi+0x180]
jmp    LOCAL+0x167
mov    al,0xa
cmp    bpl,0xf
ja     LOCAL+0x445
lea    rax,[rbp*2+0x0]
add    rax,rbp
mov    r15,rsi
cmp    QWORD PTR [rsi+rax*8+0x10],r11
jbe    LOCAL+0x808
lea    rax,[rbp*2+0x0]
add    rax,rbp
mov    rax,QWORD PTR [r15+rax*8+0x8]
mov    eax,DWORD PTR [rax+r11*4]
lea    r11d,[rax+r10*1]
cmp    r11d,0x7fffffff
lea    r15d,[rax+r10*1-0x7fffffff]
cmovb  r15d,r11d
xor    r10d,r10d
test   BYTE PTR [rdx+0x18],0x1
je     LOCAL+0x23f
movzx  r11d,WORD PTR [rdx+0x1a]
movzx  ebp,BYTE PTR [rdx+0x1c]
mov    r10d,DWORD PTR [rdx+0x20]
test   BYTE PTR [rdx+0x1e],0x1
je     LOCAL+0x1e5
mov    al,0xa
cmp    bpl,0xf
ja     LOCAL+0x445
lea    rax,[rbp*2+0x0]
add    rax,rbp
cmp    QWORD PTR [rsi+rax*8+0x190],r11
jbe    LOCAL+0x808
mov    DWORD PTR [rsp+0x8],r15d
lea    r15,[rsi+0x180]
jmp    LOCAL+0x20f
mov    al,0xa
cmp    bpl,0xf
ja     LOCAL+0x445
mov    DWORD PTR [rsp+0x8],r15d
lea    rax,[rbp*2+0x0]
add    rax,rbp
mov    r15,rsi
cmp    QWORD PTR [rsi+rax*8+0x10],r11
jbe    LOCAL+0x808
lea    rax,[rbp*2+0x0]
add    rax,rbp
mov    rax,QWORD PTR [r15+rax*8+0x8]
mov    eax,DWORD PTR [rax+r11*4]
lea    r11d,[rax+r10*1]
cmp    r11d,0x7fffffff
lea    r10d,[rax+r10*1-0x7fffffff]
cmovb  r10d,r11d
mov    r15d,DWORD PTR [rsp+0x8]
test   BYTE PTR [rdx+0x24],0x1
mov    DWORD PTR [rsp+0x78],r10d
je     LOCAL+0x297
movzx  r11d,WORD PTR [rdx+0x26]
movzx  ebp,BYTE PTR [rdx+0x28]
mov    r10d,DWORD PTR [rdx+0x2c]
test   BYTE PTR [rdx+0x2a],0x1
je     LOCAL+0x2fc
mov    al,0xa
cmp    bpl,0xf
ja     LOCAL+0x445
lea    rax,[rbp*2+0x0]
add    rax,rbp
cmp    QWORD PTR [rsi+rax*8+0x190],r11
jbe    LOCAL+0x808
mov    DWORD PTR [rsp+0x8],r15d
lea    r15,[rsi+0x180]
jmp    LOCAL+0x326
mov    QWORD PTR [rsp+0x88],0x0
xor    ebp,ebp
test   BYTE PTR [rdx+0x30],0x1
je     LOCAL+0x36a
movzx  r11d,WORD PTR [rdx+0x32]
movzx  ebp,BYTE PTR [rdx+0x34]
mov    r10d,DWORD PTR [rdx+0x38]
test   BYTE PTR [rdx+0x36],0x1
je     LOCAL+0x3cd
mov    al,0xa
cmp    bpl,0xf
ja     LOCAL+0x445
lea    rax,[rbp*2+0x0]
add    rax,rbp
cmp    QWORD PTR [rsi+rax*8+0x190],r11
jbe    LOCAL+0x808
mov    DWORD PTR [rsp+0x8],r15d
lea    r15,[rsi+0x180]
jmp    LOCAL+0x3f3
mov    al,0xa
cmp    bpl,0xf
ja     LOCAL+0x445
mov    DWORD PTR [rsp+0x8],r15d
lea    rax,[rbp*2+0x0]
add    rax,rbp
mov    r15,rsi
cmp    QWORD PTR [rsi+rax*8+0x10],r11
jbe    LOCAL+0x808
lea    rax,[rbp*2+0x0]
add    rax,rbp
mov    rax,QWORD PTR [r15+rax*8+0x8]
mov    eax,DWORD PTR [rax+r11*4]
lea    r11d,[rax+r10*1]
cmp    r11d,0x7fffffff
lea    eax,[rax+r10*1-0x7fffffff]
cmovb  eax,r11d
mov    QWORD PTR [rsp+0x88],rax
mov    r15d,DWORD PTR [rsp+0x8]
xor    ebp,ebp
test   BYTE PTR [rdx+0x30],0x1
jne    LOCAL+0x2af
mov    QWORD PTR [rsp+0x80],0x0
test   BYTE PTR [rdx+0x3c],0x1
je     LOCAL+0x49c
movzx  r11d,WORD PTR [rdx+0x3e]
movzx  ebp,BYTE PTR [rdx+0x40]
mov    r10d,DWORD PTR [rdx+0x44]
test   BYTE PTR [rdx+0x42],0x1
je     LOCAL+0x43d
mov    al,0xa
cmp    bpl,0xf
ja     LOCAL+0x445
lea    rax,[rbp*2+0x0]
add    rax,rbp
cmp    QWORD PTR [rsi+rax*8+0x190],r11
jbe    LOCAL+0x808
mov    DWORD PTR [rsp+0x8],r15d
lea    r15,[rsi+0x180]
jmp    LOCAL+0x46c
mov    al,0xa
cmp    bpl,0xf
ja     LOCAL+0x445
mov    DWORD PTR [rsp+0x8],r15d
lea    rax,[rbp*2+0x0]
add    rax,rbp
mov    r15,rsi
cmp    QWORD PTR [rsi+rax*8+0x10],r11
jbe    LOCAL+0x808
lea    rax,[rbp*2+0x0]
add    rax,rbp
mov    rax,QWORD PTR [r15+rax*8+0x8]
mov    eax,DWORD PTR [rax+r11*4]
lea    r11d,[rax+r10*1]
cmp    r11d,0x7fffffff
lea    eax,[rax+r10*1-0x7fffffff]
cmovb  eax,r11d
shl    rax,0x20
mov    QWORD PTR [rsp+0x80],rax
mov    r15d,DWORD PTR [rsp+0x8]
xor    ebp,ebp
test   BYTE PTR [rdx+0x3c],0x1
jne    LOCAL+0x380
jmp    LOCAL+0x49c
mov    al,0xa
cmp    bpl,0xf
jbe    LOCAL+0x44e
xor    ecx,ecx
xor    esi,esi
jmp    LOCAL+0x80e
mov    DWORD PTR [rsp+0x8],r15d
lea    rax,[rbp*2+0x0]
add    rax,rbp
mov    r15,rsi
cmp    QWORD PTR [rsi+rax*8+0x10],r11
jbe    LOCAL+0x808
lea    rax,[rbp*2+0x0]
add    rax,rbp
mov    rax,QWORD PTR [r15+rax*8+0x8]
mov    eax,DWORD PTR [rax+r11*4]
lea    r11d,[rax+r10*1]
cmp    r11d,0x7fffffff
lea    ebp,[rax+r10*1-0x7fffffff]
cmovb  ebp,r11d
mov    r15d,DWORD PTR [rsp+0x8]
mov    DWORD PTR [rsp+0x74],ecx
mov    QWORD PTR [rsp+0x98],r8
mov    QWORD PTR [rsp+0x90],r9
mov    QWORD PTR [rsp+0x8],rdi
mov    QWORD PTR [rsp+0x40],rdx
add    rdx,0x48
lea    rdi,[rsp+0x10]
mov    QWORD PTR [rsp+0x48],rsi
call   aspis_r1_cost_probe::host_semantic::copy_tuple_limb
movzx  ecx,BYTE PTR [rsp+0x10]
cmp    cl,0xc
jne    LOCAL+0x88f
mov    eax,DWORD PTR [rsp+0x14]
mov    DWORD PTR [rsp+0x70],eax
mov    rax,QWORD PTR [rsp+0x40]
lea    rdx,[rax+0x54]
lea    rdi,[rsp+0x10]
mov    rsi,QWORD PTR [rsp+0x48]
call   aspis_r1_cost_probe::host_semantic::copy_tuple_limb
movzx  ecx,BYTE PTR [rsp+0x10]
cmp    cl,0xc
jne    LOCAL+0x88f
mov    eax,DWORD PTR [rsp+0x14]
mov    DWORD PTR [rsp+0x6c],eax
mov    rax,QWORD PTR [rsp+0x40]
lea    rdx,[rax+0x60]
lea    rdi,[rsp+0x10]
mov    rsi,QWORD PTR [rsp+0x48]
call   aspis_r1_cost_probe::host_semantic::copy_tuple_limb
movzx  ecx,BYTE PTR [rsp+0x10]
cmp    cl,0xc
jne    LOCAL+0x88f
mov    eax,DWORD PTR [rsp+0x14]
mov    DWORD PTR [rsp+0x68],eax
mov    rax,QWORD PTR [rsp+0x40]
lea    rdx,[rax+0x6c]
lea    rdi,[rsp+0x10]
mov    rsi,QWORD PTR [rsp+0x48]
call   aspis_r1_cost_probe::host_semantic::copy_tuple_limb
movzx  ecx,BYTE PTR [rsp+0x10]
cmp    cl,0xc
jne    LOCAL+0x88f
mov    eax,DWORD PTR [rsp+0x14]
mov    DWORD PTR [rsp+0x64],eax
mov    rax,QWORD PTR [rsp+0x40]
lea    rdx,[rax+0x78]
lea    rdi,[rsp+0x10]
mov    rsi,QWORD PTR [rsp+0x48]
call   aspis_r1_cost_probe::host_semantic::copy_tuple_limb
movzx  ecx,BYTE PTR [rsp+0x10]
cmp    cl,0xc
jne    LOCAL+0x88f
mov    eax,DWORD PTR [rsp+0x14]
mov    DWORD PTR [rsp+0x60],eax
mov    rax,QWORD PTR [rsp+0x40]
lea    rdx,[rax+0x84]
lea    rdi,[rsp+0x10]
mov    rsi,QWORD PTR [rsp+0x48]
call   aspis_r1_cost_probe::host_semantic::copy_tuple_limb
movzx  ecx,BYTE PTR [rsp+0x10]
cmp    cl,0xc
jne    LOCAL+0x88f
mov    eax,DWORD PTR [rsp+0x14]
mov    DWORD PTR [rsp+0x5c],eax
mov    rax,QWORD PTR [rsp+0x40]
lea    rdx,[rax+0x90]
lea    rdi,[rsp+0x10]
mov    rsi,QWORD PTR [rsp+0x48]
call   aspis_r1_cost_probe::host_semantic::copy_tuple_limb
movzx  eax,BYTE PTR [rsp+0x10]
cmp    al,0xc
jne    LOCAL+0x8c1
mov    eax,DWORD PTR [rsp+0x14]
mov    DWORD PTR [rsp+0x58],eax
mov    rax,QWORD PTR [rsp+0x40]
lea    rdx,[rax+0x9c]
lea    rdi,[rsp+0x10]
mov    rsi,QWORD PTR [rsp+0x48]
call   aspis_r1_cost_probe::host_semantic::copy_tuple_limb
movzx  eax,BYTE PTR [rsp+0x10]
cmp    al,0xc
jne    LOCAL+0x8c1
mov    eax,DWORD PTR [rsp+0x14]
mov    DWORD PTR [rsp+0x54],eax
mov    rax,QWORD PTR [rsp+0x40]
lea    rdx,[rax+0xa8]
lea    rdi,[rsp+0x10]
mov    rsi,QWORD PTR [rsp+0x48]
call   aspis_r1_cost_probe::host_semantic::copy_tuple_limb
movzx  eax,BYTE PTR [rsp+0x10]
cmp    al,0xc
jne    LOCAL+0x8c1
mov    eax,DWORD PTR [rsp+0x14]
mov    DWORD PTR [rsp+0x50],eax
mov    rdx,QWORD PTR [rsp+0x40]
add    rdx,0xb4
lea    rdi,[rsp+0x10]
mov    rsi,QWORD PTR [rsp+0x48]
call   aspis_r1_cost_probe::host_semantic::copy_tuple_limb
movzx  eax,BYTE PTR [rsp+0x10]
cmp    al,0xc
jne    LOCAL+0x8c1
mov    rcx,QWORD PTR [rsp+0x80]
or     rcx,QWORD PTR [rsp+0x88]
mov    eax,DWORD PTR [rsp+0x7c]
mov    DWORD PTR [rsp+0xa0],eax
mov    DWORD PTR [rsp+0xa4],r15d
mov    eax,DWORD PTR [rsp+0x78]
mov    DWORD PTR [rsp+0xa8],eax
mov    QWORD PTR [rsp+0xac],rcx
mov    DWORD PTR [rsp+0xb4],ebp
mov    eax,DWORD PTR [rsp+0x70]
mov    DWORD PTR [rsp+0xb8],eax
mov    eax,DWORD PTR [rsp+0x6c]
mov    DWORD PTR [rsp+0xbc],eax
mov    eax,DWORD PTR [rsp+0x68]
mov    DWORD PTR [rsp+0xc0],eax
mov    eax,DWORD PTR [rsp+0x64]
mov    DWORD PTR [rsp+0xc4],eax
mov    eax,DWORD PTR [rsp+0x60]
mov    DWORD PTR [rsp+0xc8],eax
mov    eax,DWORD PTR [rsp+0x5c]
mov    DWORD PTR [rsp+0xcc],eax
mov    eax,DWORD PTR [rsp+0x58]
mov    DWORD PTR [rsp+0xd0],eax
mov    eax,DWORD PTR [rsp+0x54]
mov    DWORD PTR [rsp+0xd4],eax
mov    eax,DWORD PTR [rsp+0x50]
mov    DWORD PTR [rsp+0xd8],eax
mov    eax,DWORD PTR [rsp+0x14]
mov    DWORD PTR [rsp+0xdc],eax
lea    rdi,[rsp+0xe0]
lea    rdx,[rsp+0xa0]
mov    ecx,0x10
mov    esi,DWORD PTR [rsp+0x74]
mov    r8,QWORD PTR [rsp+0x98]
call   aspis_r1_cost_probe::prover_shared::compress_tagged_tuple
mov    rax,QWORD PTR [r12+0x10]
cmp    rax,rbx
jbe    LOCAL+0x90c
shl    ebx,0x6
add    rbx,QWORD PTR [r12+0x8]
mov    rax,QWORD PTR [rsp+0x90]
shl    rax,0x5
add    rax,rbx
shl    r14,0x4
movdqu xmm0,XMMWORD PTR [r14+rax*1]
paddd  xmm0,XMMWORD PTR [rsp+0xe0]
movdqa xmm1,XMMWORD PTR [RIP:DATA16:00000080000000800000008000000080]
pxor   xmm1,xmm0
pcmpeqd xmm2,xmm2
pcmpgtd xmm2,xmm1
pandn  xmm2,XMMWORD PTR [RIP:anon.19cf9f7b7bd5f5377953b3f4a1d5ab20.0.llvm.1952225316318715181+0xc0]
paddd  xmm2,xmm0
movdqu XMMWORD PTR [r14+rax*1],xmm2
mov    rax,QWORD PTR [r12+0x10]
mov    QWORD PTR [rsp+0x20],rax
movups xmm0,XMMWORD PTR [r12]
movaps XMMWORD PTR [rsp+0x10],xmm0
movups xmm1,XMMWORD PTR [r13+0x0]
movups XMMWORD PTR [rsp+0x28],xmm1
mov    rax,QWORD PTR [r13+0x10]
mov    QWORD PTR [rsp+0x38],rax
mov    rax,QWORD PTR [rsp+0x8]
movups XMMWORD PTR [rax],xmm0
mov    rcx,QWORD PTR [rsp+0x30]
mov    QWORD PTR [rax+0x20],rcx
mov    rcx,QWORD PTR [rsp+0x38]
mov    QWORD PTR [rax+0x28],rcx
mov    rcx,QWORD PTR [rsp+0x20]
mov    QWORD PTR [rax+0x10],rcx
mov    rcx,QWORD PTR [rsp+0x28]
mov    QWORD PTR [rax+0x18],rcx
jmp    LOCAL+0x87d
xor    ecx,ecx
xor    esi,esi
mov    al,0xa
shl    edx,0x8
movzx  eax,al
or     eax,edx
mov    edx,esi
or     rdx,rcx
mov    DWORD PTR [rdi+0x8],eax
mov    DWORD PTR [rdi+0xc],r8d
mov    QWORD PTR [rdi+0x10],rdx
movabs rax,0x8000000000000000
mov    QWORD PTR [rdi],rax
mov    rsi,QWORD PTR [r13+0x0]
test   rsi,rsi
je     LOCAL+0x84f
mov    rdi,QWORD PTR [r13+0x8]
shl    rsi,0x4
mov    edx,0x8
call   QWORD PTR [RIP:__rustc::__rust_dealloc]
mov    rsi,QWORD PTR [r12]
test   rsi,rsi
je     LOCAL+0x87d
mov    rdi,QWORD PTR [r12+0x8]
shl    rsi,0x6
mov    edx,0x4
add    rsp,0xf8
pop    rbx
pop    r12
pop    r13
pop    r14
pop    r15
pop    rbp
jmp    QWORD PTR [RIP:__rustc::__rust_dealloc]
add    rsp,0xf8
pop    rbx
pop    r12
pop    r13
pop    r14
pop    r15
pop    rbp
ret
movzx  eax,BYTE PTR [rsp+0x13]
shl    eax,0x10
movzx  edx,WORD PTR [rsp+0x11]
or     edx,eax
mov    eax,ecx
mov    r8d,DWORD PTR [rsp+0x14]
mov    rsi,QWORD PTR [rsp+0x18]
movabs rcx,0xffffffff00000000
and    rcx,rsi
mov    rdi,QWORD PTR [rsp+0x8]
jmp    LOCAL+0x80e
mov    r9d,eax
movzx  eax,BYTE PTR [rsp+0x13]
shl    eax,0x10
movzx  edx,WORD PTR [rsp+0x11]
or     edx,eax
mov    r8d,DWORD PTR [rsp+0x14]
mov    rsi,QWORD PTR [rsp+0x18]
movabs rcx,0xffffffff00000000
and    rcx,rsi
mov    rdi,QWORD PTR [rsp+0x8]
mov    eax,r9d
jmp    LOCAL+0x80e
lea    rdx,[RIP:anon.b35838ef3ef12f79e9725396ade5d701.34.llvm.6619295838800084750+0xf0]
mov    rdi,rbx
mov    rsi,rax
call   QWORD PTR [RIP:core::panicking::panic_bounds_check]
ud2
lea    rdx,[RIP:anon.b35838ef3ef12f79e9725396ade5d701.34.llvm.6619295838800084750+0x108]
jmp    LOCAL+0x8fe
mov    rbx,rax
mov    rsi,QWORD PTR [r13+0x0]
test   rsi,rsi
jne    LOCAL+0x932
mov    rsi,QWORD PTR [r12]
test   rsi,rsi
jne    LOCAL+0x94e
mov    rdi,rbx
call   _Unwind_Resume@plt
mov    rdi,QWORD PTR [r13+0x8]
shl    rsi,0x4
mov    edx,0x8
call   QWORD PTR [RIP:__rustc::__rust_dealloc]
mov    rsi,QWORD PTR [r12]
test   rsi,rsi
je     LOCAL+0x92a
mov    rdi,QWORD PTR [r12+0x8]
shl    rsi,0x6
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

aspis_r1_cost_probe::prover_shared::compress_tagged_tuple @ 0xcd600
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
