aspis_prover::state_only_entropy::StateOnlyAttemptSecrets::generate_for_mask_nonce @ 0x140560
push   rbp
push   r15
push   r14
push   r13
push   r12
push   rbx
sub    rsp,0x108
movdqu xmm0,XMMWORD PTR [rsi]
mov    QWORD PTR [rsp+0x58],rsi
movdqu xmm1,XMMWORD PTR [rsi+0x10]
por    xmm1,xmm0
pxor   xmm0,xmm0
pcmpeqb xmm1,xmm0
pmovmskb eax,xmm1
xor    eax,0xffff
je     LOCAL+0x1d5
mov    QWORD PTR [rsp+0x8],rdi
xor    r14d,r14d
mov    r13,QWORD PTR [RIP:_DYNAMIC+0xef8]
lea    r15,[rsp+0x10]
pxor   xmm0,xmm0
movdqa XMMWORD PTR [rsp+0x40],xmm0
movdqa XMMWORD PTR [rsp+0x30],xmm0
movdqa XMMWORD PTR [rsp+0x20],xmm0
movdqa XMMWORD PTR [rsp+0x10],xmm0
mov    rbp,QWORD PTR [r13+0x0]
test   rbp,rbp
je     LOCAL+0xcb
cmp    rbp,0xffffffffffffffff
je     LOCAL+0xe0
mov    r12d,0x40
mov    rbx,r15
mov    rdi,r15
mov    rsi,r12
xor    edx,edx
call   rbp
test   rax,rax
jle    LOCAL+0xb0
sub    r12,rax
jb     LOCAL+0x1e1
add    r15,rax
test   r12,r12
jne    LOCAL+0x82
jmp    LOCAL+0xf9
data16 data16 cs nop WORD PTR [rax+rax*1+0x0]
cmp    rax,0xffffffffffffffff
jne    LOCAL+0x1e1
call   QWORD PTR [RIP:getrandom::backends::use_file::util_libc::last_os_error]
cmp    eax,0xfffffffc
jne    LOCAL+0x1e6
jmp    LOCAL+0x9d
call   QWORD PTR [RIP:getrandom::backends::linux_android_with_fallback::init]
mov    rbp,rax
cmp    rbp,0xffffffffffffffff
jne    LOCAL+0x79
nop    WORD PTR [rax+rax*1+0x0]
mov    esi,0x40
mov    rdi,r15
call   QWORD PTR [RIP:getrandom::backends::linux_android_with_fallback::use_file_fallback]
mov    rbx,r15
test   eax,eax
jne    LOCAL+0x1e6
movdqa xmm2,XMMWORD PTR [rsp+0x10]
movdqa xmm3,XMMWORD PTR [rsp+0x20]
movdqa XMMWORD PTR [rsp+0x70],xmm3
movdqa XMMWORD PTR [rsp+0x60],xmm2
lea    rax,[rsp+0x30]
movdqu xmm0,XMMWORD PTR [rax]
movdqu xmm1,XMMWORD PTR [rax+0x10]
movdqa XMMWORD PTR [rsp+0x90],xmm1
movdqa XMMWORD PTR [rsp+0x80],xmm0
por    xmm2,xmm3
pxor   xmm3,xmm3
pcmpeqb xmm2,xmm3
pmovmskb eax,xmm2
xor    eax,0xffff
je     LOCAL+0x184
por    xmm0,xmm1
pshufd xmm1,xmm0,0xee
por    xmm1,xmm0
pshufd xmm0,xmm1,0x55
por    xmm0,xmm1
movdqa xmm1,xmm0
psrld  xmm1,0x10
por    xmm1,xmm0
movdqa xmm0,xmm1
psrlw  xmm0,0x8
por    xmm0,xmm1
movd   eax,xmm0
test   al,al
jne    LOCAL+0x230
lea    rdi,[rsp+0x80]
call   <[Z; N] as zeroize::Zeroize>::zeroize
lea    rdi,[rsp+0x60]
call   <[Z; N] as zeroize::Zeroize>::zeroize
mov    r15,rbx
inc    r14
xor    eax,eax
data16 data16 data16 cs nop WORD PTR [rax+rax*1+0x0]
lea    rcx,[rsp+rax*1]
add    rcx,0x10
mov    BYTE PTR [rsp+rax*1+0x10],0x0
inc    rax
cmp    rax,0x40
jne    LOCAL+0x1b0
cmp    r14,0x10
jne    LOCAL+0x4e
mov    rdi,QWORD PTR [rsp+0x8]
mov    DWORD PTR [rdi+0x4],0x0
mov    BYTE PTR [rdi],0x1
jmp    LOCAL+0x21b
mov    eax,0x10002
mov    rcx,QWORD PTR [rsp+0x8]
mov    DWORD PTR [rcx+0x4],eax
mov    BYTE PTR [rcx],0x1
xor    eax,eax
data16 data16 data16 cs nop WORD PTR [rax+rax*1+0x0]
lea    rcx,[rsp+rax*1]
add    rcx,0x10
mov    BYTE PTR [rsp+rax*1+0x10],0x0
inc    rax
cmp    rax,0x40
jne    LOCAL+0x200
mov    rdi,QWORD PTR [rsp+0x8]
mov    rax,rdi
add    rsp,0x108
pop    rbx
pop    r12
pop    r13
pop    r14
pop    r15
pop    rbp
ret
movdqa xmm0,XMMWORD PTR [rsp+0x10]
movdqa xmm1,XMMWORD PTR [rsp+0x20]
movdqa XMMWORD PTR [rsp+0xd0],xmm1
movdqa XMMWORD PTR [rsp+0xc0],xmm0
lea    rax,[rsp+0x30]
movdqu xmm2,XMMWORD PTR [rax]
movdqu xmm3,XMMWORD PTR [rax+0x10]
movdqa XMMWORD PTR [rsp+0xe0],xmm2
movdqa XMMWORD PTR [rsp+0xf0],xmm3
mov    rax,QWORD PTR [rsp+0x58]
movups xmm4,XMMWORD PTR [rax]
movups xmm5,XMMWORD PTR [rax+0x10]
movaps XMMWORD PTR [rsp+0xb0],xmm5
movaps XMMWORD PTR [rsp+0xa0],xmm4
mov    rax,QWORD PTR [rsp+0x8]
movdqu XMMWORD PTR [rax+0x51],xmm3
movups XMMWORD PTR [rax+0x11],xmm5
movups XMMWORD PTR [rax+0x1],xmm4
movdqu XMMWORD PTR [rax+0x41],xmm2
movdqu XMMWORD PTR [rax+0x31],xmm1
movdqu XMMWORD PTR [rax+0x21],xmm0
mov    BYTE PTR [rax],0x0
jmp    LOCAL+0x1f1
mov    rbx,rax
lea    rdi,[rsp+0x60]
call   <[Z; N] as zeroize::Zeroize>::zeroize
jmp    LOCAL+0x2cd
call   QWORD PTR [RIP:core::panicking::panic_in_cleanup]
jmp    LOCAL+0x2ca
mov    rbx,rax
xor    eax,eax
nop
lea    rcx,[rsp+rax*1]
add    rcx,0x10
mov    BYTE PTR [rsp+rax*1+0x10],0x0
inc    rax
cmp    rax,0x40
jne    LOCAL+0x2d0
mov    rdi,rbx
call   _Unwind_Resume@plt
int3
int3
