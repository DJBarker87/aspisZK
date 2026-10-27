pv_dudect::main @ 0x302a0
push   rbp
push   r15
push   r14
push   r13
push   r12
push   rbx
sub    rsp,0x568
lea    rbx,[rsp+0x548]
mov    rdi,rbx
call   QWORD PTR [RIP:std::env::args]
lea    rdi,[rsp+0x350]
mov    rsi,rbx
call   <alloc::vec::Vec<T> as alloc::vec::spec_from_iter_nested::SpecFromIterNested<T,I>>::from_iter
lea    rdx,[RIP:__frame_dummy_init_array_entry+0x348]
mov    esi,0x67
lea    rdi,[RIP:anon.4227ec7036ba7d8315078e57be449868.0.llvm.13362339970539153419+0x854]
cmp    QWORD PTR [rsp+0x360],0x3
jne    LOCAL+0x2e65
mov    rax,QWORD PTR [rsp+0x358]
cmp    QWORD PTR [rax+0x28],0x9
jne    LOCAL+0x2e65
mov    r8,QWORD PTR [rax+0x20]
movabs rcx,0x75722d7972642d2d
mov    r9,QWORD PTR [r8]
xor    r9,rcx
movzx  r10d,BYTE PTR [r8+0x8]
xor    r10,0x6e
or     r10,r9
je     LOCAL+0xa8
movabs r9,0x72757361656d2d2d
xor    r9,QWORD PTR [r8]
movzx  r10d,BYTE PTR [r8+0x8]
xor    r10,0x65
or     r10,r9
jne    LOCAL+0x2e65
xor    rcx,QWORD PTR [r8]
movzx  edx,BYTE PTR [r8+0x8]
xor    rdx,0x6e
or     rdx,rcx
setne  cl
mov    rsi,QWORD PTR [rax+0x38]
mov    rdi,QWORD PTR [rax+0x40]
cmp    rdi,0x1
je     LOCAL+0xd6
test   rdi,rdi
je     LOCAL+0x2e4b
movzx  edx,BYTE PTR [rsi]
jmp    LOCAL+0xed
movzx  edx,BYTE PTR [rsi]
mov    al,0x1
cmp    edx,0x2b
je     LOCAL+0x2930
cmp    edx,0x2d
je     LOCAL+0x2930
xor    eax,eax
cmp    dl,0x2b
sete   al
mov    rdx,rdi
sub    rdx,rax
add    rsi,rax
neg    rax
cmp    rdx,0x11
jae    LOCAL+0x276
test   rdx,rdx
je     LOCAL+0x2e30
add    rdi,rax
neg    rdi
xor    eax,eax
xor    ebx,ebx
xchg   ax,ax
movzx  edx,BYTE PTR [rsi+rax*1]
add    edx,0xffffffd0
cmp    edx,0x9
ja     LOCAL+0x2d7e
lea    r8,[rbx+rbx*4]
mov    edx,edx
lea    rbx,[rdx+r8*2]
inc    rax
mov    rdx,rdi
add    rdx,rax
jne    LOCAL+0x120
xor    eax,eax
mov    al,cl
mov    DWORD PTR [rsp+0x11c],eax
test   eax,eax
je     LOCAL+0x2cd
cmp    rbx,0xf4240
jne    LOCAL+0x2e30
lea    rsi,[RIP:anon.4227ec7036ba7d8315078e57be449868.0.llvm.13362339970539153419+0x65a]
lea    rdi,[rsp+0x260]
mov    edx,0x32
call   QWORD PTR [RIP:std::fs::read::inner]
mov    r14,QWORD PTR [rsp+0x260]
movabs rax,0x8000000000000000
cmp    r14,rax
je     LOCAL+0x2c17
mov    r12,QWORD PTR [rsp+0x268]
mov    rax,QWORD PTR [rsp+0x270]
mov    QWORD PTR [rsp+0x120],r12
mov    QWORD PTR [rsp+0x128],rax
mov    QWORD PTR [rsp+0x130],0x0
lea    rdi,[rsp+0x260]
lea    rsi,[rsp+0x120]
call   serde_json::de::from_trait
cmp    BYTE PTR [rsp+0x260],0x6
je     LOCAL+0x2c54
movupd xmm0,XMMWORD PTR [rsp+0x260]
movupd xmm1,XMMWORD PTR [rsp+0x270]
movapd XMMWORD PTR [rsp+0x130],xmm1
movapd XMMWORD PTR [rsp+0x120],xmm0
test   r14,r14
je     LOCAL+0x223
mov    edx,0x1
mov    rdi,r12
mov    rsi,r14
call   QWORD PTR [RIP:__rustc::__rust_dealloc]
lea    rdi,[RIP:anon.4227ec7036ba7d8315078e57be449868.0.llvm.13362339970539153419+0x8a4]
lea    rdx,[rsp+0x120]
mov    esi,0x5
call   QWORD PTR [RIP:<str as serde_json::value::index::Index>::index_into]
test   rax,rax
jne    LOCAL+0x249
mov    rax,QWORD PTR [RIP:_DYNAMIC+0x268]
cmp    BYTE PTR [rax],0x2
jne    LOCAL+0x2c91
mov    rcx,QWORD PTR [rax+0x8]
test   rcx,rcx
je     LOCAL+0x371
cmp    ecx,0x1
jne    LOCAL+0x393
xorps  xmm0,xmm0
cvtsi2sd xmm0,QWORD PTR [rax+0x10]
jmp    LOCAL+0x398
add    rdi,rax
neg    rdi
xor    r8d,r8d
mov    r9d,0xa
xor    ebx,ebx
nop    WORD PTR [rax+rax*1+0x0]
mov    rax,rdi
add    rax,r8
je     LOCAL+0x145
mov    rax,rbx
mul    r9
movzx  edx,BYTE PTR [rsi+r8*1]
jo     LOCAL+0x2926
add    edx,0xffffffd0
cmp    edx,0xa
jae    LOCAL+0x2d7e
mov    rbx,rax
mov    eax,edx
inc    r8
add    rbx,rax
jae    LOCAL+0x290
mov    al,0x2
jmp    LOCAL+0x2930
cmp    rbx,0x3e8
jne    LOCAL+0x2e30
lea    rsi,[RIP:anon.4227ec7036ba7d8315078e57be449868.0.llvm.13362339970539153419+0x65a]
lea    rdi,[rsp+0x260]
mov    edx,0x32
call   QWORD PTR [RIP:std::sys::fs::metadata]
cmp    DWORD PTR [rsp+0x260],0x2
jne    LOCAL+0x2e52
mov    rax,QWORD PTR [rsp+0x268]
mov    ecx,eax
and    ecx,0x3
mov    QWORD PTR [rsp+0x250],0xffffffffffffffff
mov    r13d,0x7d0
cmp    ecx,0x1
jne    LOCAL+0x447
lea    r14,[rax-0x1]
mov    r12,QWORD PTR [rax-0x1]
mov    r15,QWORD PTR [rax+0x7]
mov    rax,QWORD PTR [r15]
test   rax,rax
je     LOCAL+0x343
mov    rdi,r12
call   rax
mov    rsi,QWORD PTR [r15+0x8]
test   rsi,rsi
je     LOCAL+0x359
mov    rdx,QWORD PTR [r15+0x10]
mov    rdi,r12
call   QWORD PTR [RIP:__rustc::__rust_dealloc]
mov    esi,0x18
mov    edx,0x8
mov    rdi,r14
call   QWORD PTR [RIP:__rustc::__rust_dealloc]
jmp    LOCAL+0x447
movsd  xmm1,QWORD PTR [rax+0x10]
unpcklps xmm1,XMMWORD PTR [RIP:GCC_except_table365+0xfc]
subpd  xmm1,XMMWORD PTR [RIP:GCC_except_table365+0x3c]
movapd xmm0,xmm1
unpckhpd xmm0,xmm1
addsd  xmm0,xmm1
jmp    LOCAL+0x398
movsd  xmm0,QWORD PTR [rax+0x10]
call   QWORD PTR [RIP:floor]
cvttsd2si rax,xmm0
mov    rcx,rax
sar    rcx,0x3f
movapd xmm1,xmm0
subsd  xmm1,QWORD PTR [RIP:GCC_except_table365+0x53c]
cvttsd2si rdx,xmm1
and    rdx,rcx
or     rdx,rax
xor    eax,eax
xorpd  xmm1,xmm1
ucomisd xmm0,xmm1
cmovae rax,rdx
ucomisd xmm0,QWORD PTR [RIP:GCC_except_table365+0x4ec]
mov    rcx,0xffffffffffffffff
cmovbe rcx,rax
mov    QWORD PTR [rsp+0x250],rcx
call   QWORD PTR [RIP:std::time::SystemTime::now]
mov    QWORD PTR [rsp+0x28],rax
mov    DWORD PTR [rsp+0x30],edx
lea    rdi,[rsp+0x260]
lea    rsi,[rsp+0x28]
xor    edx,edx
xor    ecx,ecx
call   QWORD PTR [RIP:std::time::SystemTime::duration_since]
cmp    DWORD PTR [rsp+0x260],0x1
je     LOCAL+0x2caf
mov    rax,QWORD PTR [rsp+0x250]
cmp    QWORD PTR [rsp+0x268],rax
jae    LOCAL+0x2cfa
lea    rdi,[rsp+0x120]
call   core::ptr::drop_in_place<serde_json::value::Value>
mov    r13d,0x1e8480
movabs rax,0x563337342d763200
mov    QWORD PTR [rsp+0x110],rax
call   QWORD PTR [RIP:std::time::Instant::now]
mov    QWORD PTR [rsp+0x428],rbx
lea    ebx,[r13*8+0x0]
xor    esi,esi
mov    ecx,DWORD PTR [rsp+0x11c]
test   ecx,ecx
mov    QWORD PTR [rsp+0x500],rax
mov    DWORD PTR [rsp+0x508],edx
mov    edx,0x2710
cmove  rdx,rsi
lea    rax,[RIP:anon.4227ec7036ba7d8315078e57be449868.0.llvm.13362339970539153419+0x773]
lea    rsi,[RIP:anon.4227ec7036ba7d8315078e57be449868.0.llvm.13362339970539153419+0x75e]
cmove  rsi,rax
mov    QWORD PTR [rsp+0x430],rsi
mov    eax,ecx
lea    r12,[rax*4+0x11]
mov    QWORD PTR [rsp+0x20],rdx
lea    eax,[rdx*8+0x0]
mov    QWORD PTR [rsp+0x330],rax
lea    r15,[rsp+0x280]
lea    rax,[r13-0x1]
mov    QWORD PTR [rsp+0x450],rax
lea    rax,[RIP:__frame_dummy_init_array_entry+0xf8]
lea    r14,[rax+0x40]
lea    rcx,[RIP:__frame_dummy_init_array_entry+0x2b8]
mov    QWORD PTR [rsp+0x328],rcx
mov    QWORD PTR [rsp+0x340],0x0
mov    QWORD PTR [rsp+0x198],rbx
mov    QWORD PTR [rsp+0x420],r13
mov    QWORD PTR [rsp+0x438],r12
mov    QWORD PTR [rsp+0x418],r14
test   rax,rax
sete   cl
cmp    rax,r14
sete   dl
or     dl,cl
je     LOCAL+0x570
mov    rax,QWORD PTR [rsp+0x340]
cmp    rax,0xc0
je     LOCAL+0x27cf
mov    rcx,rax
lea    rax,[RIP:__frame_dummy_init_array_entry+0x138]
add    rax,rcx
add    rcx,0x10
mov    QWORD PTR [rsp+0x340],rcx
mov    QWORD PTR [rsp+0x338],0x0
jmp    LOCAL+0x57c
nop
lea    rcx,[rax+0x10]
mov    QWORD PTR [rsp+0x338],rcx
mov    QWORD PTR [rsp+0xe8],rax
call   QWORD PTR [RIP:std::time::Instant::now]
mov    QWORD PTR [rsp+0x510],rax
mov    DWORD PTR [rsp+0x518],edx
xorpd  xmm0,xmm0
movapd XMMWORD PTR [rsp+0x400],xmm0
movapd XMMWORD PTR [rsp+0x3f0],xmm0
movapd XMMWORD PTR [rsp+0x3b0],xmm0
movapd XMMWORD PTR [rsp+0x3c0],xmm0
movapd XMMWORD PTR [rsp+0x4e0],xmm0
movapd XMMWORD PTR [rsp+0x4d0],xmm0
cmp    DWORD PTR [rsp+0x11c],0x0
je     LOCAL+0x720
movabs rax,0x1b600000000
mov    QWORD PTR [rsp+0x120],rax
lea    rax,[rsp+0x128]
mov    WORD PTR [rax+0x4],0x0
mov    DWORD PTR [rax],0x0
mov    BYTE PTR [rsp+0x129],0x1
mov    BYTE PTR [rsp+0x12d],0x1
lea    rax,[rsp+0xe8]
mov    QWORD PTR [rsp+0x260],rax
lea    rax,[RIP:<&T as core::fmt::Display>::fmt]
mov    QWORD PTR [rsp+0x268],rax
lea    rdi,[rsp+0x458]
lea    rsi,[RIP:anon.b180e950c2cf49b74b4bcf8edfb7f01a.3.llvm.1180291014484726119+0x6ea]
lea    rdx,[rsp+0x260]
call   QWORD PTR [RIP:alloc::fmt::format::format_inner]
mov    r14,QWORD PTR [rsp+0x460]
mov    rcx,QWORD PTR [rsp+0x468]
lea    rdi,[rsp+0x260]
lea    rsi,[rsp+0x120]
mov    rdx,r14
call   QWORD PTR [RIP:std::fs::OpenOptions::_open]
mov    rsi,QWORD PTR [rsp+0x458]
test   rsi,rsi
je     LOCAL+0x697
mov    edx,0x1
mov    rdi,r14
call   QWORD PTR [RIP:__rustc::__rust_dealloc]
cmp    DWORD PTR [rsp+0x260],0x1
je     LOCAL+0x29cd
mov    ebp,DWORD PTR [rsp+0x264]
call   QWORD PTR [RIP:__rustc::__rust_no_alloc_shim_is_unstable_v2]
mov    edi,0x2000
mov    esi,0x1
call   QWORD PTR [RIP:__rustc::__rust_alloc]
test   rax,rax
je     LOCAL+0x2dfc
mov    QWORD PTR [rsp+0x200],0x2000
mov    QWORD PTR [rsp+0x208],rax
mov    BYTE PTR [rsp+0x218],0x0
mov    DWORD PTR [rsp+0x21c],ebp
movups xmm0,XMMWORD PTR [RIP:DATA16:782c76616c69642c6f7574636f6d650a]
movups XMMWORD PTR [rax+0x1d],xmm0
movups xmm0,XMMWORD PTR [RIP:DATA16:72745f6175782c656e645f6175782c76]
movups XMMWORD PTR [rax+0x10],xmm0
movupd xmm0,XMMWORD PTR [RIP:anon.4227ec7036ba7d8315078e57be449868.0.llvm.13362339970539153419+0x731]
movupd XMMWORD PTR [rax],xmm0
mov    QWORD PTR [rsp+0x210],0x2d
jmp    LOCAL+0x732
xchg   ax,ax
movabs rax,0x8000000000000000
mov    QWORD PTR [rsp+0x200],rax
call   QWORD PTR [RIP:__rustc::__rust_no_alloc_shim_is_unstable_v2]
mov    esi,0x8
mov    rdi,rbx
call   QWORD PTR [RIP:__rustc::__rust_alloc]
test   rax,rax
je     LOCAL+0x2dd4
mov    r14,rax
xor    eax,eax
movdqa xmm0,XMMWORD PTR [RIP:DATA16:00000000000000000100000000000000]
movdqa xmm2,XMMWORD PTR [RIP:DATA16:01000000000000000100000000000000]
movdqa xmm3,XMMWORD PTR [RIP:DATA16:04000000000000000400000000000000]
nop    DWORD PTR [rax+0x0]
movdqa xmm1,xmm0
pand   xmm1,xmm2
movdqu XMMWORD PTR [r14+rax*8],xmm1
movdqu XMMWORD PTR [r14+rax*8+0x10],xmm1
add    rax,0x4
paddq  xmm0,xmm3
cmp    r13,rax
jne    LOCAL+0x770
mov    rsi,QWORD PTR [rsp+0x110]
mov    rdi,r13
movabs rbx,0x9e3779b97f4a7c15
nop    WORD PTR [rax+rax*1+0x0]
lea    rcx,[rsi+rbx*1]
mov    rax,rcx
shr    rax,0x1e
xor    rax,rcx
movabs rdx,0xbf58476d1ce4e5b9
imul   rax,rdx
mov    rdx,rax
shr    rdx,0x1b
xor    rdx,rax
movabs rax,0x94d049bb133111eb
imul   rdx,rax
mov    rax,rdx
shr    rax,0x1f
xor    rax,rdx
xor    edx,edx
div    rdi
cmp    rdx,QWORD PTR [rsp+0x450]
ja     LOCAL+0x2d30
mov    rax,QWORD PTR [r14+rdi*8-0x8]
mov    rsi,QWORD PTR [r14+rdx*8]
mov    QWORD PTR [r14+rdi*8-0x8],rsi
dec    rdi
mov    QWORD PTR [r14+rdx*8],rax
mov    rsi,rcx
cmp    rdi,0x1
ja     LOCAL+0x7b0
mov    QWORD PTR [rsp+0x110],rcx
cmp    DWORD PTR [rsp+0x11c],0x0
je     LOCAL+0x960
call   QWORD PTR [RIP:__rustc::__rust_no_alloc_shim_is_unstable_v2]
mov    esi,0x8
mov    rdi,QWORD PTR [rsp+0x330]
call   QWORD PTR [RIP:__rustc::__rust_alloc]
test   rax,rax
je     LOCAL+0x2de7
mov    rcx,rax
mov    eax,0x6
movdqa xmm0,XMMWORD PTR [RIP:DATA16:00000000000000000100000000000000]
movdqa xmm2,XMMWORD PTR [RIP:DATA16:01000000000000000100000000000000]
movdqa xmm3,XMMWORD PTR [RIP:DATA16:08000000000000000800000000000000]
nop    WORD PTR [rax+rax*1+0x0]
movdqa xmm1,xmm0
pand   xmm1,xmm2
movdqu XMMWORD PTR [rcx+rax*8-0x30],xmm1
movdqu XMMWORD PTR [rcx+rax*8-0x20],xmm1
movdqu XMMWORD PTR [rcx+rax*8-0x10],xmm1
movdqu XMMWORD PTR [rcx+rax*8],xmm1
paddq  xmm0,xmm3
add    rax,0x8
cmp    rax,0x2716
jne    LOCAL+0x880
mov    QWORD PTR [rsp+0x238],0x2710
mov    QWORD PTR [rsp+0x240],rcx
mov    QWORD PTR [rsp+0x248],0x2710
mov    esi,0x2710
mov    rdi,QWORD PTR [rsp+0x110]
nop    DWORD PTR [rax+0x0]
lea    r8,[rdi+rbx*1]
mov    rax,r8
shr    rax,0x1e
xor    rax,r8
movabs rdx,0xbf58476d1ce4e5b9
imul   rax,rdx
mov    rdx,rax
shr    rdx,0x1b
xor    rdx,rax
movabs rax,0x94d049bb133111eb
imul   rdx,rax
mov    rax,rdx
shr    rax,0x1f
xor    rax,rdx
xor    edx,edx
div    rsi
cmp    rdx,0x2710
jae    LOCAL+0x2d56
mov    rax,QWORD PTR [rcx+rsi*8-0x8]
mov    rdi,QWORD PTR [rcx+rdx*8]
mov    QWORD PTR [rcx+rsi*8-0x8],rdi
dec    rsi
mov    QWORD PTR [rcx+rdx*8],rax
mov    rdi,r8
cmp    rsi,0x1
ja     LOCAL+0x8e0
mov    QWORD PTR [rsp+0x110],r8
mov    rsi,QWORD PTR [rsp+0x20]
jmp    LOCAL+0x986
nop    DWORD PTR [rax]
mov    QWORD PTR [rsp+0x238],0x0
mov    QWORD PTR [rsp+0x240],0x8
mov    QWORD PTR [rsp+0x248],0x0
xor    esi,esi
mov    ecx,0x8
mov    r8d,0x8
lea    rdi,[rsp+0x238]
mov    rdx,r13
call   alloc::raw_vec::RawVecInner<A>::reserve::do_reserve_and_handle
mov    rbp,r13
mov    rax,QWORD PTR [rsp+0x238]
mov    QWORD PTR [rsp+0x10],rax
mov    rbx,QWORD PTR [rsp+0x240]
mov    r13,QWORD PTR [rsp+0x248]
lea    rdi,[rbx+r13*8]
mov    rsi,r14
mov    r12,QWORD PTR [rsp+0x198]
mov    rdx,r12
call   QWORD PTR [RIP:memcpy@GLIBC_2.14]
add    r13,rbp
mov    QWORD PTR [rsp+0x248],r13
mov    edx,0x8
mov    rdi,r14
mov    rsi,r12
call   QWORD PTR [RIP:__rustc::__rust_dealloc]
lea    rax,[rbx+r13*8]
mov    rcx,QWORD PTR [rsp+0xe8]
movups xmm0,XMMWORD PTR [rcx]
mov    QWORD PTR [rsp+0x258],rbx
mov    QWORD PTR [rsp+0x520],rbx
mov    QWORD PTR [rsp+0x528],rax
lea    rax,[rsp+0x110]
mov    QWORD PTR [rsp+0x530],rax
movups XMMWORD PTR [rsp+0x538],xmm0
lea    rdi,[rsp+0x3d8]
lea    rsi,[rsp+0x520]
call   <alloc::vec::Vec<T> as alloc::vec::spec_from_iter_nested::SpecFromIterNested<T,I>>::from_iter
mov    rax,QWORD PTR [rsp+0x3e8]
cmp    rax,r13
cmovb  r13,rax
mov    QWORD PTR [rsp+0x448],r13
xorps  xmm0,xmm0
movaps XMMWORD PTR [rsp+0x4f0],xmm0
movabs rcx,0x336d712d6b73616d
movq   xmm0,rcx
movdqa XMMWORD PTR [rsp+0x370],xmm0
movabs rcx,0x6d6f646e61722d31
movq   xmm0,rcx
movdqa XMMWORD PTR [rsp+0x4b0],xmm0
movabs rcx,0x6f646e61722d3133
movq   xmm0,rcx
movdqa XMMWORD PTR [rsp+0x3a0],xmm0
movabs rcx,0x6d6f646e61722d6d
movq   xmm0,rcx
movdqa XMMWORD PTR [rsp+0x390],xmm0
movabs rcx,0x31336d2d6b73616d
movq   xmm0,rcx
movdqa XMMWORD PTR [rsp+0x380],xmm0
movabs rcx,0x2d6d6f646e61722d
movq   xmm0,rcx
movdqa XMMWORD PTR [rsp+0x490],xmm0
movabs rcx,0x2d64657869662d31
movq   xmm0,rcx
movdqa XMMWORD PTR [rsp+0x480],xmm0
movabs rcx,0x7869662d31336d71
movq   xmm0,rcx
movdqa XMMWORD PTR [rsp+0x4c0],xmm0
movabs rcx,0x64657869662d6465
movq   xmm0,rcx
movdqa XMMWORD PTR [rsp+0x4a0],xmm0
movabs rcx,0x662d64657869662d
movq   xmm0,rcx
movdqa XMMWORD PTR [rsp+0x470],xmm0
test   rax,rax
lea    rbx,[rsp+0x90]
lea    r12,[rsp+0x260]
mov    r13,QWORD PTR [rsp+0x10]
je     LOCAL+0x1a70
mov    rax,QWORD PTR [rsp+0x3e0]
mov    QWORD PTR [rsp+0x440],rax
xor    r14d,r14d
jmp    LOCAL+0xd0b
data16 data16 data16 data16 data16 cs nop WORD PTR [rax+rax*1+0x0]
inc    r14
mov    BYTE PTR [rsp+0x30],0x0
mov    BYTE PTR [rsp+0x31],0x0
mov    BYTE PTR [rsp+0x32],0x0
mov    BYTE PTR [rsp+0x33],0x0
mov    BYTE PTR [rsp+0x34],0x0
mov    BYTE PTR [rsp+0x35],0x0
mov    BYTE PTR [rsp+0x36],0x0
mov    BYTE PTR [rsp+0x37],0x0
mov    BYTE PTR [rsp+0x38],0x0
mov    BYTE PTR [rsp+0x39],0x0
mov    BYTE PTR [rsp+0x3a],0x0
mov    BYTE PTR [rsp+0x3b],0x0
mov    BYTE PTR [rsp+0x3c],0x0
mov    BYTE PTR [rsp+0x3d],0x0
mov    BYTE PTR [rsp+0x3e],0x0
mov    BYTE PTR [rsp+0x3f],0x0
mov    BYTE PTR [rsp+0x40],0x0
mov    BYTE PTR [rsp+0x41],0x0
mov    BYTE PTR [rsp+0x42],0x0
mov    BYTE PTR [rsp+0x43],0x0
mov    BYTE PTR [rsp+0x44],0x0
mov    BYTE PTR [rsp+0x45],0x0
mov    BYTE PTR [rsp+0x46],0x0
mov    BYTE PTR [rsp+0x47],0x0
mov    BYTE PTR [rsp+0x48],0x0
mov    BYTE PTR [rsp+0x49],0x0
mov    BYTE PTR [rsp+0x4a],0x0
mov    BYTE PTR [rsp+0x4b],0x0
mov    BYTE PTR [rsp+0x4c],0x0
mov    BYTE PTR [rsp+0x4d],0x0
mov    BYTE PTR [rsp+0x4e],0x0
mov    BYTE PTR [rsp+0x4f],0x0
mov    BYTE PTR [rsp+0x58],0x0
mov    BYTE PTR [rsp+0x59],0x0
mov    BYTE PTR [rsp+0x5a],0x0
mov    BYTE PTR [rsp+0x5b],0x0
mov    BYTE PTR [rsp+0x5c],0x0
mov    BYTE PTR [rsp+0x5d],0x0
mov    BYTE PTR [rsp+0x5e],0x0
mov    BYTE PTR [rsp+0x5f],0x0
mov    BYTE PTR [rsp+0x60],0x0
mov    BYTE PTR [rsp+0x61],0x0
mov    BYTE PTR [rsp+0x62],0x0
mov    BYTE PTR [rsp+0x63],0x0
mov    BYTE PTR [rsp+0x64],0x0
mov    BYTE PTR [rsp+0x65],0x0
mov    BYTE PTR [rsp+0x66],0x0
mov    BYTE PTR [rsp+0x67],0x0
mov    BYTE PTR [rsp+0x68],0x0
mov    BYTE PTR [rsp+0x69],0x0
mov    BYTE PTR [rsp+0x6a],0x0
mov    BYTE PTR [rsp+0x6b],0x0
mov    BYTE PTR [rsp+0x6c],0x0
mov    BYTE PTR [rsp+0x6d],0x0
mov    BYTE PTR [rsp+0x6e],0x0
mov    BYTE PTR [rsp+0x6f],0x0
mov    BYTE PTR [rsp+0x70],0x0
mov    BYTE PTR [rsp+0x71],0x0
mov    BYTE PTR [rsp+0x72],0x0
mov    BYTE PTR [rsp+0x73],0x0
mov    BYTE PTR [rsp+0x74],0x0
mov    BYTE PTR [rsp+0x75],0x0
mov    BYTE PTR [rsp+0x76],0x0
mov    BYTE PTR [rsp+0x77],0x0
mov    QWORD PTR [rsp+0x50],0x0
mov    QWORD PTR [rsp+0x78],0x0
cmp    r14,QWORD PTR [rsp+0x448]
lea    r12,[rsp+0x260]
je     LOCAL+0x1a70
mov    rax,QWORD PTR [rsp+0x258]
mov    rax,QWORD PTR [rax+r14*8]
mov    QWORD PTR [rsp+0x230],rax
test   r14d,0x3ff
jne    LOCAL+0xd76
call   QWORD PTR [RIP:std::time::SystemTime::now]
mov    QWORD PTR [rsp+0x80],rax
mov    DWORD PTR [rsp+0x88],edx
mov    rdi,r12
lea    rsi,[rsp+0x80]
xor    edx,edx
xor    ecx,ecx
call   QWORD PTR [RIP:std::time::SystemTime::duration_since]
cmp    DWORD PTR [rsp+0x260],0x1
je     LOCAL+0x2964
mov    rax,QWORD PTR [rsp+0x250]
cmp    QWORD PTR [rsp+0x268],rax
jae    LOCAL+0x29af
imul   rax,r14,0x74
add    rax,QWORD PTR [rsp+0x440]
xorps  xmm7,xmm7
movaps XMMWORD PTR [rsp+0x1f0],xmm7
movaps XMMWORD PTR [rsp+0x1e0],xmm7
lea    rcx,[rax+0x40]
mov    QWORD PTR [rsp+0x260],rcx
mov    QWORD PTR [rsp+0x268],0x20
mov    rsi,QWORD PTR [rsp+0x268]
cmp    rsi,0x20
jne    LOCAL+0x28c7
mov    rcx,QWORD PTR [rsp+0x260]
movups xmm0,XMMWORD PTR [rcx]
movups xmm1,XMMWORD PTR [rcx+0x10]
movaps XMMWORD PTR [rsp+0x1f0],xmm1
movaps XMMWORD PTR [rsp+0x1e0],xmm0
movups xmm0,XMMWORD PTR [rax]
movdqu xmm1,XMMWORD PTR [rax+0x10]
movdqu xmm2,XMMWORD PTR [rax+0x20]
movdqu xmm3,XMMWORD PTR [rax+0x30]
movups xmm4,XMMWORD PTR [rax+0x40]
movups xmm5,XMMWORD PTR [rax+0x50]
movups xmm6,XMMWORD PTR [rax+0x60]
mov    eax,DWORD PTR [rax+0x70]
mov    DWORD PTR [rsp+0x190],eax
movaps XMMWORD PTR [rsp+0x180],xmm6
movaps XMMWORD PTR [rsp+0x170],xmm5
movaps XMMWORD PTR [rsp+0x160],xmm4
movdqa XMMWORD PTR [rsp+0x150],xmm3
movdqa XMMWORD PTR [rsp+0x140],xmm2
movdqa XMMWORD PTR [rsp+0x130],xmm1
movaps XMMWORD PTR [rsp+0x120],xmm0
lea    rcx,[rsp+0x120]
mov    eax,DWORD PTR [rsp+0x190]
mov    DWORD PTR [rsp+0x260],eax
mov    ebp,DWORD PTR [rsp+0x260]
lea    rax,[rsp+0x128]
movdqu xmm0,XMMWORD PTR [rax+0x58]
movdqa XMMWORD PTR [rsp+0x310],xmm0
lea    rax,[rsp+0x310]
movaps XMMWORD PTR [rsp+0x1d0],xmm7
movaps XMMWORD PTR [rsp+0x1c0],xmm7
movaps XMMWORD PTR [rsp+0x1b0],xmm7
movaps XMMWORD PTR [rsp+0x1a0],xmm7
mov    QWORD PTR [rsp+0x260],rcx
mov    QWORD PTR [rsp+0x268],0x10
mov    rsi,QWORD PTR [rsp+0x268]
cmp    rsi,0x10
jne    LOCAL+0x28d5
mov    rax,QWORD PTR [rsp+0x260]
movups xmm0,XMMWORD PTR [rax]
movups xmm1,XMMWORD PTR [rax+0x10]
movdqu xmm2,XMMWORD PTR [rax+0x20]
movdqu xmm3,XMMWORD PTR [rax+0x30]
movdqa XMMWORD PTR [rsp+0x1d0],xmm3
movdqa XMMWORD PTR [rsp+0x1c0],xmm2
movaps XMMWORD PTR [rsp+0x1b0],xmm1
movaps XMMWORD PTR [rsp+0x1a0],xmm0
movdqa xmm0,XMMWORD PTR [rsp+0x1e0]
movdqa xmm1,XMMWORD PTR [rsp+0x1f0]
movdqa XMMWORD PTR [rsp+0x270],xmm1
movdqa XMMWORD PTR [rsp+0x260],xmm0
mov    rcx,QWORD PTR [rsp+0xe8]
mov    rax,QWORD PTR [rcx+0x8]
cmp    rax,0x7
jae    LOCAL+0xf40
xor    eax,eax
jmp    LOCAL+0xf76
nop    WORD PTR [rax+rax*1+0x0]
mov    rcx,QWORD PTR [rcx]
mov    edx,DWORD PTR [rcx+rax*1-0x7]
mov    esi,0x6a65722d
xor    edx,esi
mov    eax,DWORD PTR [rcx+rax*1-0x4]
mov    ecx,0x7463656a
xor    eax,ecx
or     eax,edx
cmp    QWORD PTR [rsp+0x230],0x1
mov    cl,0x2
sbb    cl,0x0
test   eax,eax
movzx  eax,cl
mov    ecx,0x0
cmovne eax,ecx
movzx  edx,al
lea    rdi,[rsp+0x28]
mov    rsi,r12
call   aspis_prover::state_only_hiding::prepare
mov    rax,QWORD PTR [rsp+0xe8]
mov    r9b,0x1
mov    r12d,0x4
cmp    QWORD PTR [rax+0x8],0x4
jne    LOCAL+0xfad
mov    rax,QWORD PTR [rax]
cmp    DWORD PTR [rax],0x656c6f70
je     LOCAL+0x10d8
xor    esi,esi
xor    r8d,r8d
cmp    r14,QWORD PTR [rsp+0x20]
mov    QWORD PTR [rsp+0x348],r8
mov    DWORD PTR [rsp+0x224],r9d
jb     LOCAL+0xfe3
mov    rdi,QWORD PTR [rsp+0x230]
cmp    rdi,0x2
jae    LOCAL+0x2d94
inc    QWORD PTR [rsp+rdi*8+0x4f0]
pcmpeqd xmm0,xmm0
movdqa XMMWORD PTR [rsp+0x2d0],xmm0
movdqa XMMWORD PTR [rsp+0x2c0],xmm0
movdqa XMMWORD PTR [rsp+0x2b0],xmm0
movdqa XMMWORD PTR [rsp+0x2a0],xmm0
movdqa XMMWORD PTR [rsp+0x290],xmm0
movdqa XMMWORD PTR [rsp+0x280],xmm0
movdqa XMMWORD PTR [rsp+0x270],xmm0
movdqa XMMWORD PTR [rsp+0x260],xmm0
mov    rax,QWORD PTR [rsp+0xe8]
mov    rcx,QWORD PTR [rax+0x8]
add    rcx,0xfffffffffffffffc
cmp    rcx,0x13
ja     LOCAL+0x14a0
mov    rax,QWORD PTR [rax]
lea    rdx,[RIP:GCC_except_table365+0x574]
movsxd rcx,DWORD PTR [rdx+rcx*4]
add    rcx,rdx
jmp    rcx
cmp    DWORD PTR [rax],0x656c6f70
jne    LOCAL+0x14a0
cmp    r14,QWORD PTR [rsp+0x20]
jae    LOCAL+0x1887
mov    QWORD PTR [rsp+0x80],r12
mov    QWORD PTR [rsp+0x88],rsi
lea    rbx,[rsp+0x80]
mov    rdi,QWORD PTR [rsp+0x80]
mov    rsi,QWORD PTR [rsp+0x88]
lea    rax,[rsp+0x260]
mov    QWORD PTR [rsp+0x80],rax
mov    rdx,QWORD PTR [rsp+0x80]
movdqu xmm0,XMMWORD PTR [RIP:DATA16:01000000000000000000000000000000]
movdqa XMMWORD PTR [rsp+0x80],xmm0
mov    rcx,rbx
call   aspis_r1_cost_probe::ct_pole::all_slots_clear
mov    BYTE PTR [rsp+0x80],al
jmp    LOCAL+0x14d3
call   QWORD PTR [RIP:__rustc::__rust_no_alloc_shim_is_unstable_v2]
mov    edi,0x10000
mov    esi,0x4
call   QWORD PTR [RIP:__rustc::__rust_alloc]
test   rax,rax
je     LOCAL+0x2dbf
mov    r12,rax
xor    eax,eax
nop    DWORD PTR [rax+0x0]
movaps xmm0,XMMWORD PTR [rsp+0x310]
movups XMMWORD PTR [rbx],xmm0
movaps xmm0,XMMWORD PTR [rsp+0x310]
movaps XMMWORD PTR [rsp+0x80],xmm0
movaps XMMWORD PTR [rsp+0x260],xmm0
movaps xmm1,XMMWORD PTR [rsp+0x90]
movaps XMMWORD PTR [rsp+0x270],xmm1
movups XMMWORD PTR [r15+0x10],xmm1
movups XMMWORD PTR [r15],xmm0
movdqa xmm0,XMMWORD PTR [rsp+0x260]
movdqa xmm1,XMMWORD PTR [rsp+0x270]
movdqa xmm2,XMMWORD PTR [rsp+0x280]
movdqa xmm3,XMMWORD PTR [rsp+0x290]
movdqu XMMWORD PTR [r12+rax*1+0x30],xmm3
movdqu XMMWORD PTR [r12+rax*1+0x20],xmm2
movdqu XMMWORD PTR [r12+rax*1+0x10],xmm1
movdqu XMMWORD PTR [r12+rax*1],xmm0
add    rax,0x40
cmp    rax,0x10000
jne    LOCAL+0x1100
mov    r8d,0x10000
mov    esi,0x400
xor    r9d,r9d
cmp    r14,QWORD PTR [rsp+0x20]
mov    QWORD PTR [rsp+0x348],r8
mov    DWORD PTR [rsp+0x224],r9d
jae    LOCAL+0xfc9
jmp    LOCAL+0xfe3
movabs rcx,0x31336d2d6b73616d
cmp    QWORD PTR [rax],rcx
je     LOCAL+0x156f
movabs rcx,0x766e692d31336d71
cmp    QWORD PTR [rax],rcx
je     LOCAL+0x183b
movabs rcx,0x73736572706d6f63
cmp    QWORD PTR [rax],rcx
jne    LOCAL+0x14a0
cmp    r14,QWORD PTR [rsp+0x20]
jae    LOCAL+0x19b6
mov    DWORD PTR [rsp+0x80],0x49
lea    rbx,[rsp+0x80]
mov    esi,DWORD PTR [rsp+0x80]
lea    rax,[rsp+0x1a0]
mov    QWORD PTR [rsp+0x80],rax
mov    QWORD PTR [rsp+0x88],0x10
mov    rdx,QWORD PTR [rsp+0x80]
mov    rcx,QWORD PTR [rsp+0x88]
movdqa xmm0,XMMWORD PTR [RIP:DATA16:0300000005000000070000000b000000]
movdqa XMMWORD PTR [rsp+0x80],xmm0
lea    rdi,[rsp+0xf0]
mov    r8,rbx
call   aspis_r1_cost_probe::prover_shared::compress_tagged_tuple
movdqu xmm0,XMMWORD PTR [rsp+0xf0]
movdqa XMMWORD PTR [rsp+0x80],xmm0
jmp    LOCAL+0x14d3
movdqu xmm0,XMMWORD PTR [rax]
pcmpeqb xmm0,XMMWORD PTR [RIP:GCC_except_table365+0x3bc]
pmovmskb eax,xmm0
cmp    eax,0xffff
jne    LOCAL+0x14a0
jmp    LOCAL+0x13f7
mov    ecx,DWORD PTR [rax]
mov    edx,0x2d31336d
xor    ecx,edx
mov    eax,DWORD PTR [rax+0x3]
mov    edx,0x766e692d
xor    eax,edx
or     eax,ecx
jne    LOCAL+0x14a0
cmp    r14,QWORD PTR [rsp+0x20]
jae    LOCAL+0x1904
mov    DWORD PTR [rsp+0x80],ebp
lea    rbx,[rsp+0x80]
mov    edi,DWORD PTR [rsp+0x80]
call   pv_dudect::inverse_m
mov    DWORD PTR [rsp+0x80],eax
jmp    LOCAL+0x14d3
movdqu xmm0,XMMWORD PTR [rax]
movdqa xmm1,XMMWORD PTR [rsp+0x380]
punpcklqdq xmm1,XMMWORD PTR [rsp+0x470]
pcmpeqb xmm1,xmm0
movd   xmm0,DWORD PTR [rax+0x10]
pcmpeqb xmm0,XMMWORD PTR [RIP:GCC_except_table365+0xdc]
pand   xmm0,xmm1
pmovmskb eax,xmm0
cmp    eax,0xffff
jne    LOCAL+0x14a0
jmp    LOCAL+0x156f
movdqa xmm0,XMMWORD PTR [rsp+0x370]
punpcklqdq xmm0,XMMWORD PTR [rsp+0x480]
movdqu xmm1,XMMWORD PTR [rax]
pcmpeqb xmm1,xmm0
movdqu xmm0,XMMWORD PTR [rax+0x5]
movdqa xmm2,XMMWORD PTR [rsp+0x4c0]
punpcklqdq xmm2,XMMWORD PTR [rsp+0x4a0]
jmp    LOCAL+0x13e0
mov    rcx,QWORD PTR [rax]
movabs rdx,0x336d712d6b73616d
xor    rcx,rdx
movzx  eax,BYTE PTR [rax+0x8]
xor    rax,0x31
or     rax,rcx
jne    LOCAL+0x14a0
jmp    LOCAL+0x13f7
mov    rcx,QWORD PTR [rax]
movabs rdx,0x31336d2d6b73616d
xor    rcx,rdx
mov    rax,QWORD PTR [rax+0x7]
movabs rdx,0x7463656a65722d31
xor    rax,rdx
or     rax,rcx
jne    LOCAL+0x14a0
jmp    LOCAL+0x156f
movdqa xmm0,XMMWORD PTR [rsp+0x370]
punpcklqdq xmm0,XMMWORD PTR [rsp+0x4b0]
movdqu xmm1,XMMWORD PTR [rax]
pcmpeqb xmm1,xmm0
movdqu xmm0,XMMWORD PTR [rax+0x7]
movdqa xmm2,XMMWORD PTR [rsp+0x3a0]
punpcklqdq xmm2,XMMWORD PTR [rsp+0x390]
pcmpeqb xmm2,xmm0
pand   xmm2,xmm1
pmovmskb eax,xmm2
cmp    eax,0xffff
jne    LOCAL+0x14a0
cmp    r14,QWORD PTR [rsp+0x20]
jae    LOCAL+0x15a9
lea    rax,[rsp+0x28]
mov    QWORD PTR [rsp+0x80],rax
lea    rdi,[rsp+0x80]
mov    rsi,QWORD PTR [rsp+0x80]
call   aspis_prover::state_only_hiding::SeedExpander::qm31
mov    eax,DWORD PTR [rsp+0x90]
mov    DWORD PTR [rsp+0x100],eax
movdqu xmm0,XMMWORD PTR [rsp+0x80]
movdqa XMMWORD PTR [rsp+0xf0],xmm0
lea    rax,[rsp+0xf0]
jmp    LOCAL+0x14d3
movdqa xmm0,XMMWORD PTR [rsp+0x380]
punpcklqdq xmm0,XMMWORD PTR [rsp+0x490]
movdqu xmm1,XMMWORD PTR [rax]
pcmpeqb xmm1,xmm0
movdqu xmm0,XMMWORD PTR [rax+0x6]
movdqa xmm2,XMMWORD PTR [rsp+0x3a0]
punpcklqdq xmm2,XMMWORD PTR [rsp+0x390]
pcmpeqb xmm2,xmm0
pand   xmm2,xmm1
pmovmskb eax,xmm2
cmp    eax,0xffff
je     LOCAL+0x156f
nop    DWORD PTR [rax+0x0]
cmp    r14,QWORD PTR [rsp+0x20]
jae    LOCAL+0x1510
lea    rax,[rsp+0x1e0]
mov    QWORD PTR [rsp+0x80],rax
lea    rbx,[rsp+0x80]
mov    rdi,QWORD PTR [rsp+0x80]
call   aspis_prover::state_only_entropy::seed_check
mov    BYTE PTR [rsp+0x80],al
mov    BYTE PTR [rsp+0xe],0x1
mov    QWORD PTR [rsp+0x368],0x0
mov    DWORD PTR [rsp+0x228],0x0
mov    DWORD PTR [rsp+0x22c],0x0
mov    BYTE PTR [rsp+0xf],0x1
jmp    LOCAL+0x17fd
data16 data16 cs nop WORD PTR [rax+rax*1+0x0]
lfence
rdtscp
mov    rbp,rax
mov    r13d,ecx
mov    rbx,rdx
lfence
lea    rax,[rsp+0x1e0]
mov    QWORD PTR [rsp+0x80],rax
lea    rax,[rsp+0x80]
mov    rdi,QWORD PTR [rsp+0x80]
call   aspis_prover::state_only_entropy::seed_check
shl    rbx,0x20
or     rbp,rbx
mov    BYTE PTR [rsp+0xe],al
lea    rax,[rsp+0xe]
lfence
rdtscp
shl    rdx,0x20
or     rdx,rax
lfence
sub    rdx,rbp
jmp    LOCAL+0x168d
cmp    r14,QWORD PTR [rsp+0x20]
jae    LOCAL+0x1629
lea    rax,[rsp+0x28]
mov    QWORD PTR [rsp+0x80],rax
lea    rbx,[rsp+0x80]
mov    rdi,QWORD PTR [rsp+0x80]
call   aspis_prover::state_only_hiding::SeedExpander::m31
mov    QWORD PTR [rsp+0x80],rax
jmp    LOCAL+0x14d3
lfence
rdtscp
mov    rbp,rax
mov    r13d,ecx
mov    rbx,rdx
lfence
lea    rax,[rsp+0x28]
mov    QWORD PTR [rsp+0x80],rax
lea    rdi,[rsp+0x80]
mov    rsi,QWORD PTR [rsp+0x80]
call   aspis_prover::state_only_hiding::SeedExpander::qm31
shl    rbx,0x20
or     rbp,rbx
mov    eax,DWORD PTR [rsp+0x90]
mov    DWORD PTR [rsp+0x100],eax
movdqu xmm0,XMMWORD PTR [rsp+0x80]
movdqa XMMWORD PTR [rsp+0xf0],xmm0
lea    rax,[rsp+0xf0]
lfence
rdtscp
shl    rdx,0x20
or     rdx,rax
lfence
sub    rdx,rbp
movzx  eax,BYTE PTR [rsp+0xf0]
jmp    LOCAL+0x1687
lfence
rdtscp
mov    rbp,rax
mov    r13d,ecx
mov    rbx,rdx
lfence
lea    rax,[rsp+0x28]
mov    QWORD PTR [rsp+0x80],rax
lea    r15,[rsp+0x80]
mov    rdi,QWORD PTR [rsp+0x80]
call   aspis_prover::state_only_hiding::SeedExpander::m31
shl    rbx,0x20
or     rbp,rbx
mov    QWORD PTR [rsp+0x80],rax
lfence
rdtscp
shl    rdx,0x20
or     rdx,rax
lfence
sub    rdx,rbp
movzx  eax,BYTE PTR [rsp+0x80]
xor    al,0x1
mov    BYTE PTR [rsp+0xe],al
mov    QWORD PTR [rsp+0x368],rdx
mov    DWORD PTR [rsp+0x228],r13d
mov    DWORD PTR [rsp+0x22c],ecx
movzx  esi,BYTE PTR [rsp+0xe]
mov    BYTE PTR [rsp+0xf],sil
mov    rdi,QWORD PTR [rsp+0x230]
cmp    rdi,0x2
lea    rbx,[rsp+0x90]
lea    r15,[rsp+0x280]
jae    LOCAL+0x2d85
mov    rax,rdi
shl    rax,0x4
lea    r8,[rsp+rax*1]
add    r8,0x4d0
inc    QWORD PTR [r8+rsi*8]
lea    rsi,[rsp+0x3c0]
cmp    r13d,ecx
sete   BYTE PTR [rsp+0x1f]
jne    LOCAL+0x1711
add    QWORD PTR [rsp+rax*1+0x3f0],rdx
adc    QWORD PTR [rsp+rax*1+0x3f8],0x0
lea    rsi,[rsp+0x3b0]
inc    QWORD PTR [rsi+rdi*8]
movabs rax,0x8000000000000000
cmp    QWORD PTR [rsp+0x200],rax
mov    r13,QWORD PTR [rsp+0x10]
je     LOCAL+0x1812
lea    rax,[rsp+0x230]
mov    QWORD PTR [rsp+0x80],rax
mov    rax,QWORD PTR [RIP:core::fmt::num::imp::<impl core::fmt::Display for u64>::fmt]
mov    QWORD PTR [rsp+0x88],rax
lea    rax,[rsp+0x368]
mov    QWORD PTR [rsp+0x90],rax
mov    rax,QWORD PTR [RIP:core::fmt::num::imp::<impl core::fmt::Display for u64>::fmt]
mov    QWORD PTR [rsp+0x98],rax
lea    rax,[rsp+0x228]
mov    QWORD PTR [rsp+0xa0],rax
mov    rax,QWORD PTR [RIP:core::fmt::num::imp::<impl core::fmt::Display for u32>::fmt]
mov    QWORD PTR [rsp+0xa8],rax
lea    rcx,[rsp+0x22c]
mov    QWORD PTR [rsp+0xb0],rcx
mov    QWORD PTR [rsp+0xb8],rax
lea    rax,[rsp+0x1f]
mov    QWORD PTR [rsp+0xc0],rax
mov    rax,QWORD PTR [RIP:<bool as core::fmt::Display>::fmt]
mov    QWORD PTR [rsp+0xc8],rax
lea    rcx,[rsp+0xf]
mov    QWORD PTR [rsp+0xd0],rcx
mov    QWORD PTR [rsp+0xd8],rax
lea    rdi,[rsp+0x200]
lea    rsi,[RIP:anon.4227ec7036ba7d8315078e57be449868.0.llvm.13362339970539153419+0x211]
lea    rdx,[rsp+0x80]
call   std::io::default_write_fmt
test   rax,rax
jne    LOCAL+0x28ec
mov    r13,QWORD PTR [rsp+0x10]
lea    rbx,[rsp+0x90]
lea    r15,[rsp+0x280]
cmp    BYTE PTR [rsp+0x224],0x0
jne    LOCAL+0xba0
mov    edx,0x4
mov    rdi,r12
mov    rsi,QWORD PTR [rsp+0x348]
call   QWORD PTR [RIP:__rustc::__rust_dealloc]
jmp    LOCAL+0xba0
cmp    r14,QWORD PTR [rsp+0x20]
jae    LOCAL+0x1944
movdqa xmm0,XMMWORD PTR [rsp+0x310]
movdqa XMMWORD PTR [rsp+0x80],xmm0
lea    rbx,[rsp+0x80]
lea    rdi,[rsp+0xf0]
mov    rsi,rbx
call   pv_dudect::inverse_q
movdqu xmm0,XMMWORD PTR [rsp+0xf0]
movdqa XMMWORD PTR [rsp+0x80],xmm0
jmp    LOCAL+0x14d3
lfence
rdtscp
mov    rbp,rax
mov    r13d,ecx
mov    rbx,rdx
lfence
mov    QWORD PTR [rsp+0x80],r12
mov    QWORD PTR [rsp+0x88],rsi
lea    rcx,[rsp+0x80]
mov    rdi,QWORD PTR [rsp+0x80]
mov    rsi,QWORD PTR [rsp+0x88]
lea    rax,[rsp+0x260]
mov    QWORD PTR [rsp+0x80],rax
mov    rdx,QWORD PTR [rsp+0x80]
movdqu xmm0,XMMWORD PTR [RIP:DATA16:01000000000000000000000000000000]
movdqa XMMWORD PTR [rsp+0x80],xmm0
call   aspis_r1_cost_probe::ct_pole::all_slots_clear
shl    rbx,0x20
or     rbp,rbx
mov    BYTE PTR [rsp+0xe],al
lea    rax,[rsp+0xe]
jmp    LOCAL+0x1557
lfence
rdtscp
mov    r15,rax
mov    r13d,ecx
mov    rbx,rdx
lfence
mov    DWORD PTR [rsp+0x80],ebp
lea    rbp,[rsp+0x80]
mov    edi,DWORD PTR [rsp+0x80]
call   pv_dudect::inverse_m
shl    rbx,0x20
or     r15,rbx
mov    DWORD PTR [rsp+0x80],eax
jmp    LOCAL+0x1a48
lfence
rdtscp
mov    rbp,rax
mov    r13d,ecx
mov    rbx,rdx
lfence
movdqa xmm0,XMMWORD PTR [rsp+0x310]
movdqa XMMWORD PTR [rsp+0x80],xmm0
lea    r15,[rsp+0x80]
lea    rdi,[rsp+0xf0]
mov    rsi,r15
call   pv_dudect::inverse_q
shl    rbx,0x20
or     rbp,rbx
movdqu xmm0,XMMWORD PTR [rsp+0xf0]
movdqa XMMWORD PTR [rsp+0x80],xmm0
lfence
rdtscp
shl    rdx,0x20
lfence
or     rdx,rax
sub    rdx,rbp
mov    BYTE PTR [rsp+0xe],0x1
jmp    LOCAL+0x168d
lfence
rdtscp
mov    r15,rax
mov    r13d,ecx
mov    rbx,rdx
lfence
mov    DWORD PTR [rsp+0x80],0x49
lea    rbp,[rsp+0x80]
mov    esi,DWORD PTR [rsp+0x80]
lea    rax,[rsp+0x1a0]
mov    QWORD PTR [rsp+0x80],rax
mov    QWORD PTR [rsp+0x88],0x10
mov    rdx,QWORD PTR [rsp+0x80]
mov    rcx,QWORD PTR [rsp+0x88]
movdqa xmm0,XMMWORD PTR [RIP:DATA16:0300000005000000070000000b000000]
movdqa XMMWORD PTR [rsp+0x80],xmm0
lea    rdi,[rsp+0xf0]
mov    r8,rbp
call   aspis_r1_cost_probe::prover_shared::compress_tagged_tuple
shl    rbx,0x20
or     r15,rbx
movdqu xmm0,XMMWORD PTR [rsp+0xf0]
movdqa XMMWORD PTR [rsp+0x80],xmm0
lfence
rdtscp
shl    rdx,0x20
lfence
or     rdx,rax
sub    rdx,r15
mov    BYTE PTR [rsp+0xe],0x1
jmp    LOCAL+0x168d
data16 cs nop WORD PTR [rax+rax*1+0x0]
movabs rax,0x8000000000000000
cmp    QWORD PTR [rsp+0x200],rax
je     LOCAL+0x1a9a
lea    rdi,[rsp+0x200]
call   std::io::buffered::bufwriter::BufWriter<W>::flush_buf
test   rax,rax
jne    LOCAL+0x2a0a
mov    QWORD PTR [rsp+0x1e0],0x0
mov    QWORD PTR [rsp+0x1f0],0x0
call   QWORD PTR [RIP:__rustc::__rust_no_alloc_shim_is_unstable_v2]
mov    r12d,0x6
mov    edi,0x6
mov    esi,0x1
call   QWORD PTR [RIP:__rustc::__rust_alloc]
test   rax,rax
je     LOCAL+0x2dac
mov    r14,rax
mov    WORD PTR [rax+0x4],0x796c
mov    DWORD PTR [rax],0x696d6166
mov    QWORD PTR [rsp+0x1a0],0x6
mov    QWORD PTR [rsp+0x1a8],rax
mov    QWORD PTR [rsp+0x1b0],0x6
mov    rax,QWORD PTR [rsp+0xe8]
mov    r12,QWORD PTR [rax+0x8]
test   r12,r12
js     LOCAL+0x27bc
mov    rbx,QWORD PTR [rax]
je     LOCAL+0x1b47
call   QWORD PTR [RIP:__rustc::__rust_no_alloc_shim_is_unstable_v2]
mov    ebp,0x1
mov    esi,0x1
mov    rdi,r12
call   QWORD PTR [RIP:__rustc::__rust_alloc]
test   rax,rax
je     LOCAL+0x27be
mov    r13,rax
jmp    LOCAL+0x1b4d
mov    r13d,0x1
mov    rdi,r13
mov    rsi,rbx
mov    rdx,r12
call   QWORD PTR [RIP:memcpy@GLIBC_2.14]
mov    BYTE PTR [rsp+0x120],0x3
mov    QWORD PTR [rsp+0x128],r12
mov    QWORD PTR [rsp+0x130],r13
mov    QWORD PTR [rsp+0x138],r12
lea    rbx,[rsp+0x80]
mov    rdi,rbx
lea    rsi,[rsp+0x1e0]
lea    rdx,[rsp+0x1a0]
lea    rcx,[rsp+0x120]
call   alloc::collections::btree::map::BTreeMap<K,V,A>::insert
cmp    BYTE PTR [rsp+0x80],0x6
mov    r13,QWORD PTR [rsp+0x10]
je     LOCAL+0x1bbb
mov    rdi,rbx
call   core::ptr::drop_in_place<serde_json::value::Value>
call   QWORD PTR [RIP:__rustc::__rust_no_alloc_shim_is_unstable_v2]
mov    r12d,0x5
mov    edi,0x5
mov    esi,0x1
call   QWORD PTR [RIP:__rustc::__rust_alloc]
test   rax,rax
je     LOCAL+0x2dac
mov    r14,rax
mov    BYTE PTR [rax+0x4],0x6c
mov    DWORD PTR [rax],0x6562616c
mov    QWORD PTR [rsp+0x1a0],0x5
mov    QWORD PTR [rsp+0x1a8],rax
mov    QWORD PTR [rsp+0x1b0],0x5
call   QWORD PTR [RIP:__rustc::__rust_no_alloc_shim_is_unstable_v2]
mov    esi,0x1
mov    r12,QWORD PTR [rsp+0x438]
mov    rdi,r12
call   QWORD PTR [RIP:__rustc::__rust_alloc]
test   rax,rax
je     LOCAL+0x2e0e
mov    rbx,rax
mov    rdi,rax
mov    rsi,QWORD PTR [rsp+0x430]
mov    rdx,r12
call   QWORD PTR [RIP:memcpy@GLIBC_2.14]
mov    BYTE PTR [rsp+0x120],0x3
mov    QWORD PTR [rsp+0x128],r12
mov    QWORD PTR [rsp+0x130],rbx
mov    QWORD PTR [rsp+0x138],r12
lea    rbx,[rsp+0x80]
mov    rdi,rbx
lea    rsi,[rsp+0x1e0]
lea    rdx,[rsp+0x1a0]
lea    rcx,[rsp+0x120]
call   alloc::collections::btree::map::BTreeMap<K,V,A>::insert
cmp    BYTE PTR [rsp+0x80],0x6
je     LOCAL+0x1ca3
mov    rdi,rbx
call   core::ptr::drop_in_place<serde_json::value::Value>
call   QWORD PTR [RIP:__rustc::__rust_no_alloc_shim_is_unstable_v2]
mov    r12d,0x9
mov    edi,0x9
mov    esi,0x1
call   QWORD PTR [RIP:__rustc::__rust_alloc]
test   rax,rax
je     LOCAL+0x2dac
movabs rcx,0x73616c635f726570
mov    QWORD PTR [rax],rcx
mov    BYTE PTR [rax+0x8],0x73
mov    QWORD PTR [rsp+0x1a0],0x9
mov    QWORD PTR [rsp+0x1a8],rax
mov    QWORD PTR [rsp+0x1b0],0x9
mov    BYTE PTR [rsp+0x120],0x2
mov    QWORD PTR [rsp+0x128],0x0
mov    rax,QWORD PTR [rsp+0x428]
mov    QWORD PTR [rsp+0x130],rax
mov    rdi,rbx
lea    rsi,[rsp+0x1e0]
lea    rdx,[rsp+0x1a0]
lea    rcx,[rsp+0x120]
call   alloc::collections::btree::map::BTreeMap<K,V,A>::insert
cmp    BYTE PTR [rsp+0x80],0x6
je     LOCAL+0x1d4f
mov    rdi,rbx
call   core::ptr::drop_in_place<serde_json::value::Value>
call   QWORD PTR [RIP:__rustc::__rust_no_alloc_shim_is_unstable_v2]
mov    r12d,0xb
mov    edi,0xb
mov    esi,0x1
call   QWORD PTR [RIP:__rustc::__rust_alloc]
test   rax,rax
je     LOCAL+0x2dac
mov    r14,rax
movabs rax,0x7461726170657270
mov    QWORD PTR [r14],rax
mov    DWORD PTR [r14+0x7],0x6e6f6974
mov    QWORD PTR [rsp+0x1a0],0xb
mov    QWORD PTR [rsp+0x1a8],r14
mov    QWORD PTR [rsp+0x1b0],0xb
call   QWORD PTR [RIP:__rustc::__rust_no_alloc_shim_is_unstable_v2]
mov    edi,0x2a
mov    esi,0x1
call   QWORD PTR [RIP:__rustc::__rust_alloc]
test   rax,rax
je     LOCAL+0x2e1e
movups xmm0,XMMWORD PTR [RIP:DATA16:6f6e2066726573682062756666657273]
movups XMMWORD PTR [rax+0x1a],xmm0
movups xmm0,XMMWORD PTR [RIP:DATA16:6f7264733b20636f6d6d6f6e20667265]
movups XMMWORD PTR [rax+0x10],xmm0
movdqu xmm0,XMMWORD PTR [RIP:DATA16:70726567656e65726174656420726563]
movdqu XMMWORD PTR [rax],xmm0
mov    BYTE PTR [rsp+0x120],0x3
mov    QWORD PTR [rsp+0x128],0x2a
mov    QWORD PTR [rsp+0x130],rax
mov    QWORD PTR [rsp+0x138],0x2a
mov    rdi,rbx
lea    rsi,[rsp+0x1e0]
lea    rdx,[rsp+0x1a0]
lea    rcx,[rsp+0x120]
call   alloc::collections::btree::map::BTreeMap<K,V,A>::insert
cmp    BYTE PTR [rsp+0x80],0x6
je     LOCAL+0x1e47
mov    rdi,rbx
call   core::ptr::drop_in_place<serde_json::value::Value>
call   QWORD PTR [RIP:__rustc::__rust_no_alloc_shim_is_unstable_v2]
mov    r12d,0x18
mov    edi,0x18
mov    esi,0x1
call   QWORD PTR [RIP:__rustc::__rust_alloc]
test   rax,rax
je     LOCAL+0x2dac
mov    r14,rax
movups xmm0,XMMWORD PTR [RIP:DATA16:66726573685f70726570617265645f70]
movups XMMWORD PTR [rax],xmm0
movabs rax,0x7373616c635f7265
mov    QWORD PTR [r14+0x10],rax
mov    QWORD PTR [rsp+0x1a0],0x18
mov    QWORD PTR [rsp+0x1a8],r14
mov    QWORD PTR [rsp+0x1b0],0x18
lea    rdi,[rsp+0x120]
lea    rsi,[rsp+0x4f0]
call   serde_json::value::to_value
cmp    BYTE PTR [rsp+0x120],0x6
je     LOCAL+0x2a3f
movdqu xmm0,XMMWORD PTR [rsp+0x120]
movdqu xmm1,XMMWORD PTR [rsp+0x130]
movdqa XMMWORD PTR [rsp+0x90],xmm1
movdqa XMMWORD PTR [rsp+0x80],xmm0
lea    rdi,[rsp+0x120]
lea    rsi,[rsp+0x1e0]
lea    rdx,[rsp+0x1a0]
mov    rcx,rbx
call   alloc::collections::btree::map::BTreeMap<K,V,A>::insert
cmp    BYTE PTR [rsp+0x120],0x6
je     LOCAL+0x1f25
lea    rdi,[rsp+0x120]
call   core::ptr::drop_in_place<serde_json::value::Value>
call   QWORD PTR [RIP:__rustc::__rust_no_alloc_shim_is_unstable_v2]
mov    r12d,0xe
mov    edi,0xe
mov    esi,0x1
call   QWORD PTR [RIP:__rustc::__rust_alloc]
test   rax,rax
je     LOCAL+0x2dac
movabs rcx,0x6c6f72746e6f635f
mov    QWORD PTR [rax+0x6],rcx
movabs rcx,0x635f7974696e6173
mov    QWORD PTR [rax],rcx
mov    QWORD PTR [rsp+0x1a0],0xe
mov    QWORD PTR [rsp+0x1a8],rax
mov    QWORD PTR [rsp+0x1b0],0xe
mov    rax,QWORD PTR [rsp+0xe8]
mov    rcx,QWORD PTR [rax+0x8]
add    rcx,0xffffffffffffffec
cmp    rcx,0x3
ja     LOCAL+0x208f
mov    rax,QWORD PTR [rax]
lea    rdx,[RIP:GCC_except_table365+0x5c4]
movsxd rcx,DWORD PTR [rdx+rcx*4]
add    rcx,rdx
jmp    rcx
movdqu xmm0,XMMWORD PTR [rax]
movdqa xmm1,XMMWORD PTR [rsp+0x380]
punpcklqdq xmm1,XMMWORD PTR [rsp+0x470]
pcmpeqb xmm1,xmm0
movd   xmm0,DWORD PTR [rax+0x10]
pcmpeqb xmm0,XMMWORD PTR [RIP:GCC_except_table365+0xdc]
pand   xmm0,xmm1
pmovmskb eax,xmm0
cmp    eax,0xffff
jne    LOCAL+0x208f
mov    al,0x1
jmp    LOCAL+0x2091
movdqa xmm1,XMMWORD PTR [rsp+0x380]
punpcklqdq xmm1,XMMWORD PTR [rsp+0x490]
movdqu xmm0,XMMWORD PTR [rax]
pcmpeqb xmm0,xmm1
movdqu xmm1,XMMWORD PTR [rax+0x6]
jmp    LOCAL+0x2033
movdqa xmm1,XMMWORD PTR [rsp+0x370]
punpcklqdq xmm1,XMMWORD PTR [rsp+0x4b0]
movdqu xmm0,XMMWORD PTR [rax]
pcmpeqb xmm0,xmm1
movdqu xmm1,XMMWORD PTR [rax+0x7]
movdqa xmm2,XMMWORD PTR [rsp+0x3a0]
punpcklqdq xmm2,XMMWORD PTR [rsp+0x390]
jmp    LOCAL+0x2078
movdqa xmm1,XMMWORD PTR [rsp+0x370]
punpcklqdq xmm1,XMMWORD PTR [rsp+0x480]
movdqu xmm0,XMMWORD PTR [rax]
pcmpeqb xmm0,xmm1
movdqu xmm1,XMMWORD PTR [rax+0x5]
movdqa xmm2,XMMWORD PTR [rsp+0x4c0]
punpcklqdq xmm2,XMMWORD PTR [rsp+0x4a0]
pcmpeqb xmm2,xmm1
pand   xmm2,xmm0
pmovmskb eax,xmm2
cmp    eax,0xffff
je     LOCAL+0x1fec
xor    eax,eax
mov    BYTE PTR [rsp+0x120],0x1
mov    BYTE PTR [rsp+0x121],al
mov    rdi,rbx
lea    rsi,[rsp+0x1e0]
lea    rdx,[rsp+0x1a0]
lea    rcx,[rsp+0x120]
call   alloc::collections::btree::map::BTreeMap<K,V,A>::insert
cmp    BYTE PTR [rsp+0x80],0x6
je     LOCAL+0x20d2
mov    rdi,rbx
call   core::ptr::drop_in_place<serde_json::value::Value>
call   QWORD PTR [RIP:__rustc::__rust_no_alloc_shim_is_unstable_v2]
mov    r12d,0x5
mov    edi,0x5
mov    esi,0x1
call   QWORD PTR [RIP:__rustc::__rust_alloc]
test   rax,rax
je     LOCAL+0x2dac
mov    r14,rax
mov    BYTE PTR [rax+0x4],0x64
mov    DWORD PTR [rax],0x696c6176
mov    QWORD PTR [rsp+0x1a0],0x5
mov    QWORD PTR [rsp+0x1a8],rax
mov    QWORD PTR [rsp+0x1b0],0x5
lea    rdi,[rsp+0x120]
lea    rsi,[rsp+0x3b0]
call   serde_json::value::to_value
cmp    BYTE PTR [rsp+0x120],0x6
je     LOCAL+0x2a7c
movdqu xmm0,XMMWORD PTR [rsp+0x120]
movdqu xmm1,XMMWORD PTR [rsp+0x130]
movdqa XMMWORD PTR [rsp+0x90],xmm1
movdqa XMMWORD PTR [rsp+0x80],xmm0
lea    rdi,[rsp+0x120]
lea    rsi,[rsp+0x1e0]
lea    rdx,[rsp+0x1a0]
mov    rcx,rbx
call   alloc::collections::btree::map::BTreeMap<K,V,A>::insert
cmp    BYTE PTR [rsp+0x120],0x6
je     LOCAL+0x21a2
lea    rdi,[rsp+0x120]
call   core::ptr::drop_in_place<serde_json::value::Value>
call   QWORD PTR [RIP:__rustc::__rust_no_alloc_shim_is_unstable_v2]
mov    r12d,0xa
mov    edi,0xa
mov    esi,0x1
call   QWORD PTR [RIP:__rustc::__rust_alloc]
test   rax,rax
je     LOCAL+0x2dac
mov    r14,rax
movabs rax,0x6f6974617267696d
mov    QWORD PTR [r14],rax
mov    WORD PTR [r14+0x8],0x736e
mov    QWORD PTR [rsp+0x1a0],0xa
mov    QWORD PTR [rsp+0x1a8],r14
mov    QWORD PTR [rsp+0x1b0],0xa
lea    rdi,[rsp+0x120]
lea    rsi,[rsp+0x3c0]
call   serde_json::value::to_value
cmp    BYTE PTR [rsp+0x120],0x6
je     LOCAL+0x2ab9
movdqu xmm0,XMMWORD PTR [rsp+0x120]
movdqu xmm1,XMMWORD PTR [rsp+0x130]
movdqa XMMWORD PTR [rsp+0x90],xmm1
movdqa XMMWORD PTR [rsp+0x80],xmm0
lea    rdi,[rsp+0x120]
lea    rsi,[rsp+0x1e0]
lea    rdx,[rsp+0x1a0]
mov    rcx,rbx
call   alloc::collections::btree::map::BTreeMap<K,V,A>::insert
cmp    BYTE PTR [rsp+0x120],0x6
je     LOCAL+0x227c
lea    rdi,[rsp+0x120]
call   core::ptr::drop_in_place<serde_json::value::Value>
call   QWORD PTR [RIP:__rustc::__rust_no_alloc_shim_is_unstable_v2]
mov    r12d,0x13
mov    edi,0x13
mov    esi,0x1
call   QWORD PTR [RIP:__rustc::__rust_alloc]
test   rax,rax
je     LOCAL+0x2dac
mov    r14,rax
movups xmm0,XMMWORD PTR [RIP:DATA16:6f7574636f6d65735f66616c73655f74]
movups XMMWORD PTR [rax],xmm0
mov    DWORD PTR [rax+0xf],0x65757274
mov    QWORD PTR [rsp+0x1a0],0x13
mov    QWORD PTR [rsp+0x1a8],rax
mov    QWORD PTR [rsp+0x1b0],0x13
lea    rdi,[rsp+0x120]
lea    rsi,[rsp+0x4d0]
call   serde_json::value::to_value
cmp    BYTE PTR [rsp+0x120],0x6
je     LOCAL+0x2af6
movupd xmm0,XMMWORD PTR [rsp+0x120]
movdqu xmm1,XMMWORD PTR [rsp+0x130]
movdqa XMMWORD PTR [rsp+0x90],xmm1
movapd XMMWORD PTR [rsp+0x80],xmm0
lea    rdi,[rsp+0x120]
lea    rsi,[rsp+0x1e0]
lea    rdx,[rsp+0x1a0]
mov    rcx,rbx
call   alloc::collections::btree::map::BTreeMap<K,V,A>::insert
cmp    BYTE PTR [rsp+0x120],0x6
je     LOCAL+0x2353
lea    rdi,[rsp+0x120]
call   core::ptr::drop_in_place<serde_json::value::Value>
call   QWORD PTR [RIP:__rustc::__rust_no_alloc_shim_is_unstable_v2]
mov    r12d,0xb
mov    edi,0xb
mov    esi,0x1
call   QWORD PTR [RIP:__rustc::__rust_alloc]
test   rax,rax
je     LOCAL+0x2dac
mov    r14,rax
movabs rax,0x6379635f6e61656d
mov    QWORD PTR [r14],rax
mov    DWORD PTR [r14+0x7],0x73656c63
mov    QWORD PTR [rsp+0x1a0],0xb
mov    QWORD PTR [rsp+0x1a8],r14
mov    QWORD PTR [rsp+0x1b0],0xb
call   QWORD PTR [RIP:__rustc::__rust_no_alloc_shim_is_unstable_v2]
mov    edi,0x40
mov    esi,0x8
call   QWORD PTR [RIP:__rustc::__rust_alloc]
test   rax,rax
je     LOCAL+0x2b33
mov    r12,rax
mov    rdi,QWORD PTR [rsp+0x3f0]
mov    rsi,QWORD PTR [rsp+0x3f8]
call   QWORD PTR [RIP:__floatuntidf]
movsd  xmm1,QWORD PTR [rsp+0x3b0]
unpcklps xmm1,XMMWORD PTR [RIP:GCC_except_table365+0xfc]
subpd  xmm1,XMMWORD PTR [RIP:GCC_except_table365+0x3c]
movapd xmm2,xmm1
unpckhpd xmm2,xmm1
addsd  xmm2,xmm1
divsd  xmm0,xmm2
lea    rdi,[rsp+0x120]
call   QWORD PTR [RIP:serde_json::value::from::<impl core::convert::From<f64> for serde_json::value::Value>::from]
cmp    BYTE PTR [rsp+0x120],0x6
je     LOCAL+0x2b48
movupd xmm0,XMMWORD PTR [rsp+0x120]
movups xmm1,XMMWORD PTR [rsp+0x130]
movaps XMMWORD PTR [rsp+0x90],xmm1
movapd XMMWORD PTR [rsp+0x80],xmm0
mov    rdi,QWORD PTR [rsp+0x400]
mov    rsi,QWORD PTR [rsp+0x408]
call   QWORD PTR [RIP:__floatuntidf]
movsd  xmm1,QWORD PTR [rsp+0x3b8]
unpcklps xmm1,XMMWORD PTR [RIP:GCC_except_table365+0xfc]
subpd  xmm1,XMMWORD PTR [RIP:GCC_except_table365+0x3c]
movapd xmm2,xmm1
unpckhpd xmm2,xmm1
addsd  xmm2,xmm1
divsd  xmm0,xmm2
lea    rdi,[rsp+0x120]
call   QWORD PTR [RIP:serde_json::value::from::<impl core::convert::From<f64> for serde_json::value::Value>::from]
cmp    BYTE PTR [rsp+0x120],0x6
je     LOCAL+0x2b85
movups xmm0,XMMWORD PTR [rsp+0x120]
movups xmm1,XMMWORD PTR [rsp+0x130]
movups XMMWORD PTR [r12+0x30],xmm1
movups XMMWORD PTR [r12+0x20],xmm0
movapd xmm0,XMMWORD PTR [rsp+0x80]
movapd xmm1,XMMWORD PTR [rsp+0x90]
movupd XMMWORD PTR [r12+0x10],xmm1
movupd XMMWORD PTR [r12],xmm0
mov    QWORD PTR [rsp+0x128],0x2
mov    QWORD PTR [rsp+0x130],r12
mov    QWORD PTR [rsp+0x138],0x2
mov    BYTE PTR [rsp+0x120],0x4
mov    rdi,rbx
lea    rsi,[rsp+0x1e0]
lea    rdx,[rsp+0x1a0]
lea    rcx,[rsp+0x120]
call   alloc::collections::btree::map::BTreeMap<K,V,A>::insert
cmp    BYTE PTR [rsp+0x80],0x6
je     LOCAL+0x253d
mov    rdi,rbx
call   core::ptr::drop_in_place<serde_json::value::Value>
call   QWORD PTR [RIP:__rustc::__rust_no_alloc_shim_is_unstable_v2]
mov    r12d,0xc
mov    edi,0xc
mov    esi,0x1
call   QWORD PTR [RIP:__rustc::__rust_alloc]
test   rax,rax
je     LOCAL+0x2dac
mov    r14,rax
movabs rax,0x6365735f6c6c6177
mov    QWORD PTR [r14],rax
mov    DWORD PTR [r14+0x8],0x73646e6f
mov    QWORD PTR [rsp+0x1a0],0xc
mov    QWORD PTR [rsp+0x1a8],r14
mov    QWORD PTR [rsp+0x1b0],0xc
lea    rdi,[rsp+0x510]
call   QWORD PTR [RIP:std::time::Instant::elapsed]
movq   xmm0,rax
punpckldq xmm0,XMMWORD PTR [RIP:GCC_except_table365+0xfc]
subpd  xmm0,XMMWORD PTR [RIP:GCC_except_table365+0x3c]
movapd xmm1,xmm0
unpckhpd xmm1,xmm0
addsd  xmm1,xmm0
xorps  xmm0,xmm0
cvtsi2sd xmm0,edx
divsd  xmm0,QWORD PTR [RIP:GCC_except_table365+0x4f4]
addsd  xmm0,xmm1
lea    rdi,[rsp+0x120]
call   QWORD PTR [RIP:serde_json::value::from::<impl core::convert::From<f64> for serde_json::value::Value>::from]
cmp    BYTE PTR [rsp+0x120],0x6
je     LOCAL+0x2bc2
movdqu xmm0,XMMWORD PTR [rsp+0x120]
movdqu xmm1,XMMWORD PTR [rsp+0x130]
movdqa XMMWORD PTR [rsp+0x90],xmm1
movdqa XMMWORD PTR [rsp+0x80],xmm0
lea    rdi,[rsp+0x120]
lea    rsi,[rsp+0x1e0]
lea    rdx,[rsp+0x1a0]
mov    rcx,rbx
call   alloc::collections::btree::map::BTreeMap<K,V,A>::insert
cmp    BYTE PTR [rsp+0x120],0x6
je     LOCAL+0x2653
lea    rdi,[rsp+0x120]
call   core::ptr::drop_in_place<serde_json::value::Value>
mov    rax,QWORD PTR [rsp+0x1f0]
lea    rcx,[rsp+0x30]
mov    QWORD PTR [rcx+0x10],rax
movdqu xmm0,XMMWORD PTR [rsp+0x1e0]
movdqu XMMWORD PTR [rcx],xmm0
mov    BYTE PTR [rsp+0x28],0x5
lea    rbx,[rsp+0x28]
mov    QWORD PTR [rsp+0x260],rbx
mov    rax,QWORD PTR [RIP:<serde_json::value::Value as core::fmt::Display>::fmt]
mov    QWORD PTR [rsp+0x268],rax
lea    rdi,[RIP:anon.d5090c25a416dcf11afff7dd91233e4e.0.llvm.13100340739265517091+0x127]
lea    rsi,[rsp+0x260]
call   QWORD PTR [RIP:std::io::stdio::_print]
mov    rdi,rbx
call   core::ptr::drop_in_place<serde_json::value::Value>
mov    rax,QWORD PTR [rsp+0xe8]
cmp    QWORD PTR [rax+0x8],0x5
jb     LOCAL+0x26f0
mov    rax,QWORD PTR [rax]
mov    ecx,DWORD PTR [rax]
mov    edx,0x6b73616d
xor    ecx,edx
movzx  eax,BYTE PTR [rax+0x4]
xor    eax,0x2d
or     eax,ecx
jne    LOCAL+0x26f0
mov    rax,QWORD PTR [rsp+0x4e0]
or     rax,QWORD PTR [rsp+0x4d0]
jne    LOCAL+0x2d18
nop    DWORD PTR [rax+rax*1+0x0]
mov    rax,QWORD PTR [rsp+0x3c0]
or     rax,QWORD PTR [rsp+0x3c8]
jne    LOCAL+0x2bff
mov    rax,QWORD PTR [rsp+0x3d8]
test   rax,rax
je     LOCAL+0x272a
mov    rdi,QWORD PTR [rsp+0x3e0]
imul   rsi,rax,0x74
mov    edx,0x4
call   QWORD PTR [RIP:__rustc::__rust_dealloc]
test   r13,r13
mov    r14,QWORD PTR [rsp+0x418]
je     LOCAL+0x2751
shl    r13,0x3
mov    edx,0x8
mov    rdi,QWORD PTR [rsp+0x258]
mov    rsi,r13
call   QWORD PTR [RIP:__rustc::__rust_dealloc]
movabs rax,0x8000000000000000
cmp    QWORD PTR [rsp+0x200],rax
mov    rbx,QWORD PTR [rsp+0x198]
mov    r13,QWORD PTR [rsp+0x420]
je     LOCAL+0x27af
lea    rdi,[rsp+0x200]
call   <std::io::buffered::bufwriter::BufWriter<W> as core::ops::drop::Drop>::drop
mov    rsi,QWORD PTR [rsp+0x200]
test   rsi,rsi
je     LOCAL+0x27a2
mov    rdi,QWORD PTR [rsp+0x208]
mov    edx,0x1
call   QWORD PTR [RIP:__rustc::__rust_dealloc]
mov    edi,DWORD PTR [rsp+0x21c]
call   QWORD PTR [RIP:close@GLIBC_2.2.5]
mov    rax,QWORD PTR [rsp+0x338]
jmp    LOCAL+0x524
xor    ebp,ebp
mov    rdi,rbp
mov    rsi,r12
call   QWORD PTR [RIP:alloc::raw_vec::handle_error]
jmp    LOCAL+0x2e6b
lea    rdi,[rsp+0x500]
call   QWORD PTR [RIP:std::time::Instant::elapsed]
movq   xmm0,rax
punpckldq xmm0,XMMWORD PTR [RIP:GCC_except_table365+0xfc]
subpd  xmm0,XMMWORD PTR [RIP:GCC_except_table365+0x3c]
movapd xmm1,xmm0
unpckhpd xmm1,xmm0
cvtsi2sd xmm2,edx
addsd  xmm1,xmm0
divsd  xmm2,QWORD PTR [RIP:GCC_except_table365+0x4f4]
addsd  xmm2,xmm1
movsd  QWORD PTR [rsp+0x120],xmm2
lea    rax,[rsp+0x120]
mov    QWORD PTR [rsp+0x260],rax
mov    rax,QWORD PTR [RIP:core::fmt::float::<impl core::fmt::Display for f64>::fmt]
mov    QWORD PTR [rsp+0x268],rax
lea    rdi,[RIP:anon.4227ec7036ba7d8315078e57be449868.0.llvm.13362339970539153419+0x1ab]
lea    rsi,[rsp+0x260]
call   QWORD PTR [RIP:std::io::stdio::_eprint]
mov    rbx,QWORD PTR [rsp+0x358]
mov    r14,QWORD PTR [rsp+0x360]
test   r14,r14
je     LOCAL+0x2892
lea    r15,[rbx+0x8]
jmp    LOCAL+0x2879
cs nop WORD PTR [rax+rax*1+0x0]
add    r15,0x18
dec    r14
je     LOCAL+0x2892
mov    rsi,QWORD PTR [r15-0x8]
test   rsi,rsi
je     LOCAL+0x2870
mov    rdi,QWORD PTR [r15]
mov    edx,0x1
call   QWORD PTR [RIP:__rustc::__rust_dealloc]
jmp    LOCAL+0x2870
mov    rax,QWORD PTR [rsp+0x350]
test   rax,rax
je     LOCAL+0x28b5
shl    rax,0x3
lea    rsi,[rax+rax*2]
mov    edx,0x8
mov    rdi,rbx
call   QWORD PTR [RIP:__rustc::__rust_dealloc]
add    rsp,0x568
pop    rbx
pop    r12
pop    r13
pop    r14
pop    r15
pop    rbp
ret
mov    edi,0x20
lea    rdx,[RIP:__frame_dummy_init_array_entry+0x288]
jmp    LOCAL+0x28e1
mov    edi,0x10
lea    rdx,[RIP:__frame_dummy_init_array_entry+0x2a0]
call   QWORD PTR [RIP:core::slice::copy_from_slice_impl::len_mismatch_fail]
jmp    LOCAL+0x2e6b
mov    QWORD PTR [rsp+0xf0],rax
lea    rdi,[RIP:GCC_except_table365+0x5d4]
lea    rcx,[RIP:__frame_dummy_init_array_entry+0x8]
lea    r8,[RIP:__frame_dummy_init_array_entry+0x2e8]
lea    rdx,[rsp+0xf0]
mov    esi,0x2b
mov    r13,QWORD PTR [rsp+0x10]
call   QWORD PTR [RIP:core::result::unwrap_failed]
jmp    LOCAL+0x2e6b
add    dl,0xd0
xor    eax,eax
cmp    dl,0xa
adc    al,0x1
mov    BYTE PTR [rsp+0x260],al
lea    rdi,[RIP:GCC_except_table365+0x5d4]
lea    rcx,[RIP:__frame_dummy_init_array_entry+0x48]
lea    r8,[RIP:__frame_dummy_init_array_entry+0xc8]
lea    rdx,[rsp+0x260]
mov    esi,0x2b
call   QWORD PTR [RIP:core::result::unwrap_failed]
jmp    LOCAL+0x2e6b
mov    rax,QWORD PTR [rsp+0x268]
mov    ecx,DWORD PTR [rsp+0x270]
mov    QWORD PTR [rsp+0x120],rax
mov    DWORD PTR [rsp+0x128],ecx
lea    rdi,[RIP:GCC_except_table365+0x5d4]
lea    rcx,[RIP:__frame_dummy_init_array_entry+0x28]
lea    r8,[RIP:__frame_dummy_init_array_entry+0x360]
lea    rdx,[rsp+0x120]
mov    esi,0x2b
call   QWORD PTR [RIP:core::result::unwrap_failed]
jmp    LOCAL+0x2e6b
mov    esi,0x1d
lea    rdi,[RIP:anon.4227ec7036ba7d8315078e57be449868.0.llvm.13362339970539153419+0x824]
lea    rdx,[RIP:__frame_dummy_init_array_entry+0x270]
call   QWORD PTR [RIP:core::panicking::panic_fmt]
jmp    LOCAL+0x2e6b
mov    rax,QWORD PTR [rsp+0x268]
mov    QWORD PTR [rsp+0x80],rax
lea    rdi,[RIP:GCC_except_table365+0x5d4]
lea    rcx,[RIP:__frame_dummy_init_array_entry+0x8]
lea    r8,[RIP:__frame_dummy_init_array_entry+0x1f8]
lea    rdx,[rsp+0x80]
mov    esi,0x2b
call   QWORD PTR [RIP:core::result::unwrap_failed]
jmp    LOCAL+0x2e6b
mov    QWORD PTR [rsp+0x260],rax
lea    rdi,[RIP:GCC_except_table365+0x5d4]
lea    rcx,[RIP:__frame_dummy_init_array_entry+0x8]
lea    r8,[RIP:__frame_dummy_init_array_entry+0x210]
lea    rdx,[rsp+0x260]
mov    esi,0x2b
call   QWORD PTR [RIP:core::result::unwrap_failed]
jmp    LOCAL+0x2e6b
mov    rax,QWORD PTR [rsp+0x128]
mov    QWORD PTR [rsp+0x80],rax
lea    rdi,[RIP:GCC_except_table365+0x5d4]
lea    rcx,[RIP:__frame_dummy_init_array_entry+0x68]
lea    r8,[RIP:__frame_dummy_init_array_entry+0x228]
lea    rdx,[rsp+0x80]
mov    esi,0x2b
call   QWORD PTR [RIP:core::result::unwrap_failed]
jmp    LOCAL+0x2e6b
mov    rax,QWORD PTR [rsp+0x128]
mov    QWORD PTR [rsp+0x80],rax
lea    rdi,[RIP:GCC_except_table365+0x5d4]
lea    rcx,[RIP:__frame_dummy_init_array_entry+0x68]
lea    r8,[RIP:__frame_dummy_init_array_entry+0x228]
lea    rdx,[rsp+0x80]
mov    esi,0x2b
call   QWORD PTR [RIP:core::result::unwrap_failed]
jmp    LOCAL+0x2e6b
mov    rax,QWORD PTR [rsp+0x128]
mov    QWORD PTR [rsp+0x80],rax
lea    rdi,[RIP:GCC_except_table365+0x5d4]
lea    rcx,[RIP:__frame_dummy_init_array_entry+0x68]
lea    r8,[RIP:__frame_dummy_init_array_entry+0x228]
lea    rdx,[rsp+0x80]
mov    esi,0x2b
call   QWORD PTR [RIP:core::result::unwrap_failed]
jmp    LOCAL+0x2e6b
mov    rax,QWORD PTR [rsp+0x128]
mov    QWORD PTR [rsp+0x80],rax
lea    rdi,[RIP:GCC_except_table365+0x5d4]
lea    rcx,[RIP:__frame_dummy_init_array_entry+0x68]
lea    r8,[RIP:__frame_dummy_init_array_entry+0x228]
lea    rdx,[rsp+0x80]
mov    esi,0x2b
call   QWORD PTR [RIP:core::result::unwrap_failed]
jmp    LOCAL+0x2e6b
mov    edi,0x8
mov    esi,0x40
call   QWORD PTR [RIP:alloc::alloc::handle_alloc_error]
jmp    LOCAL+0x2e6b
mov    rax,QWORD PTR [rsp+0x128]
mov    QWORD PTR [rsp+0x80],rax
lea    rdi,[RIP:GCC_except_table365+0x5d4]
lea    rcx,[RIP:__frame_dummy_init_array_entry+0x68]
lea    r8,[RIP:__frame_dummy_init_array_entry+0x228]
lea    rdx,[rsp+0x80]
mov    esi,0x2b
call   QWORD PTR [RIP:core::result::unwrap_failed]
jmp    LOCAL+0x2e6b
mov    rax,QWORD PTR [rsp+0x128]
mov    QWORD PTR [rsp+0xf0],rax
lea    rdi,[RIP:GCC_except_table365+0x5d4]
lea    rcx,[RIP:__frame_dummy_init_array_entry+0x68]
lea    r8,[RIP:__frame_dummy_init_array_entry+0x228]
lea    rdx,[rsp+0xf0]
mov    esi,0x2b
call   QWORD PTR [RIP:core::result::unwrap_failed]
jmp    LOCAL+0x2e6b
mov    rax,QWORD PTR [rsp+0x128]
mov    QWORD PTR [rsp+0x80],rax
lea    rdi,[RIP:GCC_except_table365+0x5d4]
lea    rcx,[RIP:__frame_dummy_init_array_entry+0x68]
lea    r8,[RIP:__frame_dummy_init_array_entry+0x228]
lea    rdx,[rsp+0x80]
mov    esi,0x2b
call   QWORD PTR [RIP:core::result::unwrap_failed]
jmp    LOCAL+0x2e6b
mov    esi,0x55
lea    rdi,[RIP:anon.4227ec7036ba7d8315078e57be449868.0.llvm.13362339970539153419+0x7d9]
lea    rdx,[RIP:__frame_dummy_init_array_entry+0x240]
jmp    LOCAL+0x29c2
mov    rax,QWORD PTR [rsp+0x268]
mov    QWORD PTR [rsp+0x120],rax
lea    rdi,[RIP:anon.4227ec7036ba7d8315078e57be449868.0.llvm.13362339970539153419+0x887]
lea    rcx,[RIP:__frame_dummy_init_array_entry+0x8]
lea    r8,[RIP:__frame_dummy_init_array_entry+0x378]
lea    rdx,[rsp+0x120]
mov    esi,0x1d
call   QWORD PTR [RIP:core::result::unwrap_failed]
jmp    LOCAL+0x2e6b
mov    rax,QWORD PTR [rsp+0x268]
mov    QWORD PTR [rsp+0x120],rax
lea    rdi,[RIP:GCC_except_table365+0x5d4]
lea    rcx,[RIP:__frame_dummy_init_array_entry+0x68]
lea    r8,[RIP:__frame_dummy_init_array_entry+0x390]
lea    rdx,[rsp+0x120]
mov    esi,0x2b
call   QWORD PTR [RIP:core::result::unwrap_failed]
jmp    LOCAL+0x2e6b
lea    rdi,[RIP:anon.4227ec7036ba7d8315078e57be449868.0.llvm.13362339970539153419+0x8a9]
lea    rdx,[RIP:__frame_dummy_init_array_entry+0x3c0]
mov    esi,0xd
call   QWORD PTR [RIP:core::option::expect_failed]
jmp    LOCAL+0x2e6b
mov    rax,QWORD PTR [rsp+0x268]
mov    ecx,DWORD PTR [rsp+0x270]
mov    QWORD PTR [rsp+0x80],rax
mov    DWORD PTR [rsp+0x88],ecx
lea    rdi,[RIP:GCC_except_table365+0x5d4]
lea    rcx,[RIP:__frame_dummy_init_array_entry+0x28]
lea    r8,[RIP:__frame_dummy_init_array_entry+0x360]
lea    rdx,[rsp+0x80]
mov    esi,0x2b
call   QWORD PTR [RIP:core::result::unwrap_failed]
jmp    LOCAL+0x2e6b
lea    rdi,[RIP:anon.4227ec7036ba7d8315078e57be449868.0.llvm.13362339970539153419+0x824]
lea    rdx,[RIP:__frame_dummy_init_array_entry+0x3a8]
mov    esi,0x1d
call   QWORD PTR [RIP:core::panicking::panic_fmt]
jmp    LOCAL+0x2e6b
mov    esi,0x43
lea    rdi,[RIP:anon.4227ec7036ba7d8315078e57be449868.0.llvm.13362339970539153419+0x803]
lea    rdx,[RIP:__frame_dummy_init_array_entry+0x258]
jmp    LOCAL+0x29c2
add    rsi,rbx
mov    QWORD PTR [rsp+0x110],rsi
lea    rax,[RIP:__frame_dummy_init_array_entry+0x318]
mov    rdi,rdx
mov    rsi,r13
mov    rdx,rax
call   QWORD PTR [RIP:core::panicking::panic_bounds_check]
jmp    LOCAL+0x2e6b
add    rdi,rbx
mov    QWORD PTR [rsp+0x110],rdi
lea    rax,[RIP:__frame_dummy_init_array_entry+0x300]
mov    rdi,rdx
mov    rsi,QWORD PTR [rsp+0x20]
mov    rdx,rax
call   QWORD PTR [RIP:core::panicking::panic_bounds_check]
jmp    LOCAL+0x2e6b
mov    al,0x1
jmp    LOCAL+0x2930
lea    rax,[RIP:__frame_dummy_init_array_entry+0x2d0]
mov    QWORD PTR [rsp+0x328],rax
mov    esi,0x2
mov    rdx,QWORD PTR [rsp+0x328]
call   QWORD PTR [RIP:core::panicking::panic_bounds_check]
jmp    LOCAL+0x2e6b
mov    edi,0x1
mov    rsi,r12
call   QWORD PTR [RIP:alloc::raw_vec::handle_error]
jmp    LOCAL+0x2e6b
mov    edi,0x4
mov    esi,0x10000
call   QWORD PTR [RIP:alloc::raw_vec::handle_error]
jmp    LOCAL+0x2e6b
mov    edi,0x8
mov    rsi,rbx
call   QWORD PTR [RIP:alloc::raw_vec::handle_error]
jmp    LOCAL+0x2e6b
mov    edi,0x8
mov    rsi,QWORD PTR [rsp+0x330]
call   QWORD PTR [RIP:alloc::raw_vec::handle_error]
jmp    LOCAL+0x2e6b
mov    edi,0x1
mov    esi,0x2000
call   QWORD PTR [RIP:alloc::raw_vec::handle_error]
jmp    LOCAL+0x2e6b
mov    edi,0x1
mov    rsi,r12
call   QWORD PTR [RIP:alloc::raw_vec::handle_error]
jmp    LOCAL+0x2e6b
mov    edi,0x1
mov    esi,0x2a
call   QWORD PTR [RIP:alloc::raw_vec::handle_error]
jmp    LOCAL+0x2e6b
lea    rdi,[RIP:anon.4227ec7036ba7d8315078e57be449868.0.llvm.13362339970539153419+0x61c]
lea    rdx,[RIP:__frame_dummy_init_array_entry+0xe0]
mov    esi,0x3e
call   QWORD PTR [RIP:core::panicking::panic]
jmp    LOCAL+0x2e6b
xor    eax,eax
jmp    LOCAL+0x2930
lea    rdx,[RIP:__frame_dummy_init_array_entry+0x330]
mov    esi,0x45
lea    rdi,[RIP:anon.4227ec7036ba7d8315078e57be449868.0.llvm.13362339970539153419+0x832]
call   QWORD PTR [RIP:core::panicking::panic_fmt]
ud2
mov    rbx,rax
mov    rsi,QWORD PTR [r15+0x8]
test   rsi,rsi
je     LOCAL+0x2e86
mov    rdx,QWORD PTR [r15+0x10]
mov    rdi,r12
call   QWORD PTR [RIP:__rustc::__rust_dealloc]
mov    esi,0x18
mov    edx,0x8
jmp    LOCAL+0x2f5b
mov    rbx,rax
jmp    LOCAL+0x34fb
mov    rbx,rax
jmp    LOCAL+0x304b
mov    rbx,rax
lea    rdi,[rsp+0x28]
call   core::ptr::drop_in_place<serde_json::value::Value>
jmp    LOCAL+0x3494
jmp    LOCAL+0x2fbf
jmp    LOCAL+0x2fbf
mov    rbx,rax
jmp    LOCAL+0x30bb
mov    rbx,rax
jmp    LOCAL+0x30e0
jmp    LOCAL+0x2fbf
mov    rbx,rax
jmp    LOCAL+0x311a
jmp    LOCAL+0x2fbf
mov    rbx,rax
jmp    LOCAL+0x3137
jmp    LOCAL+0x2fbf
mov    rbx,rax
jmp    LOCAL+0x3154
jmp    LOCAL+0x2fbf
jmp    LOCAL+0x2fbf
mov    rbx,rax
jmp    LOCAL+0x3171
jmp    LOCAL+0x2fbf
jmp    LOCAL+0x2fbf
jmp    LOCAL+0x2fbf
jmp    LOCAL+0x2fd4
mov    rbx,rax
mov    esi,0xb
jmp    LOCAL+0x33fc
mov    rbx,rax
mov    esi,0x5
jmp    LOCAL+0x33fc
mov    rbx,rax
mov    edi,ebp
jmp    LOCAL+0x3522
mov    rbx,rax
mov    rsi,QWORD PTR [rsp+0x458]
test   rsi,rsi
je     LOCAL+0x3528
mov    edx,0x1
mov    rdi,r14
call   QWORD PTR [RIP:__rustc::__rust_dealloc]
jmp    LOCAL+0x3528
jmp    LOCAL+0x3026
mov    rbx,rax
jmp    LOCAL+0x309b
jmp    LOCAL+0x33ec
mov    rbx,rax
mov    r13,QWORD PTR [rsp+0x10]
jmp    LOCAL+0x34b8
mov    rbx,rax
mov    edx,0x8
mov    rdi,r14
mov    rsi,QWORD PTR [rsp+0x198]
call   QWORD PTR [RIP:__rustc::__rust_dealloc]
xor    ebp,ebp
mov    rax,QWORD PTR [rsp+0x238]
mov    QWORD PTR [rsp+0x20],rax
jmp    LOCAL+0x2fe4
mov    rbx,rax
jmp    LOCAL+0x34da
jmp    LOCAL+0x33e4
mov    rbx,rax
jmp    LOCAL+0x340f
mov    rbx,rax
mov    r13,QWORD PTR [rsp+0x10]
jmp    LOCAL+0x325c
mov    rbx,rax
jmp    LOCAL+0x340a
jmp    LOCAL+0x301e
mov    rbx,rax
mov    bpl,0x1
cmp    QWORD PTR [rsp+0x20],0x0
je     LOCAL+0x3008
mov    rdi,QWORD PTR [rsp+0x240]
mov    rsi,QWORD PTR [rsp+0x20]
shl    rsi,0x3
mov    edx,0x8
call   QWORD PTR [RIP:__rustc::__rust_dealloc]
test   bpl,bpl
mov    rsi,QWORD PTR [rsp+0x198]
jne    LOCAL+0x34cc
jmp    LOCAL+0x34da
mov    rbx,rax
jmp    LOCAL+0x3237
mov    rbx,rax
mov    rsi,QWORD PTR [rsp+0x198]
jmp    LOCAL+0x34cc
jmp    LOCAL+0x33ec
mov    rbx,rax
lea    rdi,[rsp+0x120]
call   core::ptr::drop_in_place<serde_json::error::Error>
test   r14,r14
je     LOCAL+0x3528
mov    edx,0x1
mov    rdi,r12
mov    rsi,r14
call   QWORD PTR [RIP:__rustc::__rust_dealloc]
jmp    LOCAL+0x3528
call   QWORD PTR [RIP:core::panicking::panic_in_cleanup]
mov    rbx,rax
lea    rdi,[rsp+0x120]
call   core::ptr::drop_in_place<std::io::error::Error>
jmp    LOCAL+0x3528
call   QWORD PTR [RIP:core::panicking::panic_in_cleanup]
mov    rbx,rax
lea    rdi,[rsp+0x80]
call   core::ptr::drop_in_place<serde_json::error::Error>
mov    esi,0xc
jmp    LOCAL+0x3176
call   QWORD PTR [RIP:core::panicking::panic_in_cleanup]
mov    rbx,rax
lea    rdi,[rsp+0xf0]
call   core::ptr::drop_in_place<serde_json::error::Error>
lea    rdi,[rsp+0x80]
call   core::ptr::drop_in_place<serde_json::value::Value>
jmp    LOCAL+0x30e0
call   QWORD PTR [RIP:core::panicking::panic_in_cleanup]
mov    rbx,rax
lea    rdi,[rsp+0x80]
call   core::ptr::drop_in_place<serde_json::error::Error>
mov    esi,0x40
mov    edx,0x8
mov    rdi,r12
call   QWORD PTR [RIP:__rustc::__rust_dealloc]
mov    esi,0xb
jmp    LOCAL+0x3176
call   QWORD PTR [RIP:core::panicking::panic_in_cleanup]
mov    rbx,rax
mov    esi,0xb
jmp    LOCAL+0x3176
mov    rbx,rax
lea    rdi,[rsp+0x80]
call   core::ptr::drop_in_place<serde_json::error::Error>
mov    esi,0x13
jmp    LOCAL+0x3176
call   QWORD PTR [RIP:core::panicking::panic_in_cleanup]
mov    rbx,rax
lea    rdi,[rsp+0x80]
call   core::ptr::drop_in_place<serde_json::error::Error>
mov    esi,0xa
jmp    LOCAL+0x3176
call   QWORD PTR [RIP:core::panicking::panic_in_cleanup]
mov    rbx,rax
lea    rdi,[rsp+0x80]
call   core::ptr::drop_in_place<serde_json::error::Error>
mov    esi,0x5
jmp    LOCAL+0x3176
call   QWORD PTR [RIP:core::panicking::panic_in_cleanup]
mov    rbx,rax
lea    rdi,[rsp+0x80]
call   core::ptr::drop_in_place<serde_json::error::Error>
mov    esi,0x18
mov    edx,0x1
mov    rdi,r14
call   QWORD PTR [RIP:__rustc::__rust_dealloc]
jmp    LOCAL+0x340f
call   QWORD PTR [RIP:core::panicking::panic_in_cleanup]
mov    rbx,rax
lea    rdi,[rsp+0x260]
call   core::ptr::drop_in_place<std::io::error::Error>
jmp    LOCAL+0x3494
call   QWORD PTR [RIP:core::panicking::panic_in_cleanup]
mov    rbx,rax
lea    rdi,[rsp+0x80]
call   core::ptr::drop_in_place<std::io::error::Error>
jmp    LOCAL+0x3528
call   QWORD PTR [RIP:core::panicking::panic_in_cleanup]
mov    rbx,rax
lea    rdi,[rsp+0x120]
call   core::ptr::drop_in_place<serde_json::value::Value>
jmp    LOCAL+0x3528
call   QWORD PTR [RIP:core::panicking::panic_in_cleanup]
mov    rbx,rax
mov    rax,QWORD PTR [rsp+0xf0]
mov    ecx,eax
and    ecx,0x3
cmp    ecx,0x1
jne    LOCAL+0x323c
lea    r15,[rax-0x1]
mov    r13,QWORD PTR [rax-0x1]
mov    r14,QWORD PTR [rax+0x7]
mov    rax,QWORD PTR [r14]
test   rax,rax
je     LOCAL+0x320e
mov    rdi,r13
call   rax
mov    rsi,QWORD PTR [r14+0x8]
test   rsi,rsi
je     LOCAL+0x3224
mov    rdx,QWORD PTR [r14+0x10]
mov    rdi,r13
call   QWORD PTR [RIP:__rustc::__rust_dealloc]
mov    esi,0x18
mov    edx,0x8
mov    rdi,r15
call   QWORD PTR [RIP:__rustc::__rust_dealloc]
mov    r13,QWORD PTR [rsp+0x10]
cmp    BYTE PTR [rsp+0x224],0x0
jne    LOCAL+0x325c
mov    edx,0x4
mov    rdi,r12
mov    rsi,QWORD PTR [rsp+0x348]
call   QWORD PTR [RIP:__rustc::__rust_dealloc]
mov    BYTE PTR [rsp+0x30],0x0
mov    BYTE PTR [rsp+0x31],0x0
mov    BYTE PTR [rsp+0x32],0x0
mov    BYTE PTR [rsp+0x33],0x0
mov    BYTE PTR [rsp+0x34],0x0
mov    BYTE PTR [rsp+0x35],0x0
mov    BYTE PTR [rsp+0x36],0x0
mov    BYTE PTR [rsp+0x37],0x0
mov    BYTE PTR [rsp+0x38],0x0
mov    BYTE PTR [rsp+0x39],0x0
mov    BYTE PTR [rsp+0x3a],0x0
mov    BYTE PTR [rsp+0x3b],0x0
mov    BYTE PTR [rsp+0x3c],0x0
mov    BYTE PTR [rsp+0x3d],0x0
mov    BYTE PTR [rsp+0x3e],0x0
mov    BYTE PTR [rsp+0x3f],0x0
mov    BYTE PTR [rsp+0x40],0x0
mov    BYTE PTR [rsp+0x41],0x0
mov    BYTE PTR [rsp+0x42],0x0
mov    BYTE PTR [rsp+0x43],0x0
mov    BYTE PTR [rsp+0x44],0x0
mov    BYTE PTR [rsp+0x45],0x0
mov    BYTE PTR [rsp+0x46],0x0
mov    BYTE PTR [rsp+0x47],0x0
mov    BYTE PTR [rsp+0x48],0x0
mov    BYTE PTR [rsp+0x49],0x0
mov    BYTE PTR [rsp+0x4a],0x0
mov    BYTE PTR [rsp+0x4b],0x0
mov    BYTE PTR [rsp+0x4c],0x0
mov    BYTE PTR [rsp+0x4d],0x0
mov    BYTE PTR [rsp+0x4e],0x0
mov    BYTE PTR [rsp+0x4f],0x0
mov    BYTE PTR [rsp+0x58],0x0
mov    BYTE PTR [rsp+0x59],0x0
mov    BYTE PTR [rsp+0x5a],0x0
mov    BYTE PTR [rsp+0x5b],0x0
mov    BYTE PTR [rsp+0x5c],0x0
mov    BYTE PTR [rsp+0x5d],0x0
mov    BYTE PTR [rsp+0x5e],0x0
mov    BYTE PTR [rsp+0x5f],0x0
mov    BYTE PTR [rsp+0x60],0x0
mov    BYTE PTR [rsp+0x61],0x0
mov    BYTE PTR [rsp+0x62],0x0
mov    BYTE PTR [rsp+0x63],0x0
mov    BYTE PTR [rsp+0x64],0x0
mov    BYTE PTR [rsp+0x65],0x0
mov    BYTE PTR [rsp+0x66],0x0
mov    BYTE PTR [rsp+0x67],0x0
mov    BYTE PTR [rsp+0x68],0x0
mov    BYTE PTR [rsp+0x69],0x0
mov    BYTE PTR [rsp+0x6a],0x0
mov    BYTE PTR [rsp+0x6b],0x0
mov    BYTE PTR [rsp+0x6c],0x0
mov    BYTE PTR [rsp+0x6d],0x0
mov    BYTE PTR [rsp+0x6e],0x0
mov    BYTE PTR [rsp+0x6f],0x0
mov    BYTE PTR [rsp+0x70],0x0
mov    BYTE PTR [rsp+0x71],0x0
mov    BYTE PTR [rsp+0x72],0x0
mov    BYTE PTR [rsp+0x73],0x0
mov    BYTE PTR [rsp+0x74],0x0
mov    BYTE PTR [rsp+0x75],0x0
mov    BYTE PTR [rsp+0x76],0x0
mov    BYTE PTR [rsp+0x77],0x0
mov    QWORD PTR [rsp+0x50],0x0
mov    QWORD PTR [rsp+0x78],0x0
jmp    LOCAL+0x3494
mov    rsi,QWORD PTR [r14+0x8]
test   rsi,rsi
je     LOCAL+0x33c9
mov    rdx,QWORD PTR [r14+0x10]
mov    rdi,r13
call   QWORD PTR [RIP:__rustc::__rust_dealloc]
mov    esi,0x18
mov    edx,0x8
mov    rdi,r15
call   QWORD PTR [RIP:__rustc::__rust_dealloc]
call   QWORD PTR [RIP:core::panicking::panic_in_cleanup]
jmp    LOCAL+0x33ec
mov    rbx,rax
jmp    LOCAL+0x3528
mov    rbx,rax
jmp    LOCAL+0x3494
mov    rbx,rax
mov    esi,0x6
mov    edx,0x1
mov    rdi,r14
call   QWORD PTR [RIP:__rustc::__rust_dealloc]
mov    r13,QWORD PTR [rsp+0x10]
mov    rcx,QWORD PTR [rsp+0x1e0]
test   rcx,rcx
jne    LOCAL+0x3422
xor    ecx,ecx
xor    eax,eax
jmp    LOCAL+0x346f
mov    rdx,QWORD PTR [rsp+0x1e8]
mov    rax,QWORD PTR [rsp+0x1f0]
mov    QWORD PTR [rsp+0x268],0x0
mov    QWORD PTR [rsp+0x270],rcx
mov    QWORD PTR [rsp+0x278],rdx
mov    QWORD PTR [rsp+0x288],0x0
mov    QWORD PTR [rsp+0x290],rcx
mov    QWORD PTR [rsp+0x298],rdx
mov    ecx,0x1
mov    QWORD PTR [rsp+0x260],rcx
mov    QWORD PTR [rsp+0x280],rcx
mov    QWORD PTR [rsp+0x2a0],rax
lea    rdi,[rsp+0x260]
call   core::ptr::drop_in_place<alloc::collections::btree::map::IntoIter<alloc::string::String,serde_json::value::Value>>
mov    rax,QWORD PTR [rsp+0x3d8]
test   rax,rax
je     LOCAL+0x34b8
mov    rdi,QWORD PTR [rsp+0x3e0]
imul   rsi,rax,0x74
mov    edx,0x4
call   QWORD PTR [RIP:__rustc::__rust_dealloc]
test   r13,r13
je     LOCAL+0x34da
shl    r13,0x3
mov    rsi,r13
mov    r14,QWORD PTR [rsp+0x258]
mov    edx,0x8
mov    rdi,r14
call   QWORD PTR [RIP:__rustc::__rust_dealloc]
movabs rax,0x8000000000000000
cmp    QWORD PTR [rsp+0x200],rax
je     LOCAL+0x3528
lea    rdi,[rsp+0x200]
call   <std::io::buffered::bufwriter::BufWriter<W> as core::ops::drop::Drop>::drop
mov    rsi,QWORD PTR [rsp+0x200]
test   rsi,rsi
je     LOCAL+0x351b
mov    rdi,QWORD PTR [rsp+0x208]
mov    edx,0x1
call   QWORD PTR [RIP:__rustc::__rust_dealloc]
mov    edi,DWORD PTR [rsp+0x21c]
call   QWORD PTR [RIP:close@GLIBC_2.2.5]
mov    r14,QWORD PTR [rsp+0x358]
mov    r15,QWORD PTR [rsp+0x360]
test   r15,r15
jne    LOCAL+0x3568
mov    rax,QWORD PTR [rsp+0x350]
test   rax,rax
je     LOCAL+0x3560
shl    rax,0x3
lea    rsi,[rax+rax*2]
mov    edx,0x8
mov    rdi,r14
call   QWORD PTR [RIP:__rustc::__rust_dealloc]
mov    rdi,rbx
call   _Unwind_Resume@plt
lea    r12,[r14+0x8]
mov    r13,QWORD PTR [RIP:__rustc::__rust_dealloc]
jmp    LOCAL+0x3589
data16 cs nop WORD PTR [rax+rax*1+0x0]
add    r12,0x18
dec    r15
je     LOCAL+0x353d
mov    rsi,QWORD PTR [r12-0x8]
test   rsi,rsi
je     LOCAL+0x3580
mov    rdi,QWORD PTR [r12]
mov    edx,0x1
call   r13
jmp    LOCAL+0x3580
mov    rsi,QWORD PTR [rsp+0x200]
test   rsi,rsi
je     LOCAL+0x35c1
mov    rdi,QWORD PTR [rsp+0x208]
mov    edx,0x1
call   QWORD PTR [RIP:__rustc::__rust_dealloc]
mov    edi,DWORD PTR [rsp+0x21c]
call   QWORD PTR [RIP:close@GLIBC_2.2.5]
call   QWORD PTR [RIP:core::panicking::panic_in_cleanup]
call   QWORD PTR [RIP:core::panicking::panic_in_cleanup]
int3
int3
int3
int3
int3
int3

pv_dudect::inverse_m @ 0x339e0
jmp    QWORD PTR [RIP:aspis_core::field::M31::inv]
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

pv_dudect::inverse_q @ 0x339f0
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

pv_dudect::kernels::state_only_hiding::measure_m31 @ 0x380d0
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
lea    rax,[RIP:anon.d47d9abe28adb0f891ea640ec8a3320f.4.llvm.12847193204274187099+0x43]
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
lea    rcx,[RIP:anon.d47d9abe28adb0f891ea640ec8a3320f.6.llvm.12847193204274187099+0x18]
mov    edx,0x20
call   QWORD PTR [RIP:core::slice::index::slice_index_fail]

pv_dudect::kernels::state_only_hiding::measure_qm31 @ 0x38220
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
lea    rax,[RIP:anon.d47d9abe28adb0f891ea640ec8a3320f.4.llvm.12847193204274187099+0x43]
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
lea    rax,[RIP:anon.d47d9abe28adb0f891ea640ec8a3320f.4.llvm.12847193204274187099+0x43]
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
lea    rax,[RIP:anon.d47d9abe28adb0f891ea640ec8a3320f.4.llvm.12847193204274187099+0x43]
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
lea    rax,[RIP:anon.d47d9abe28adb0f891ea640ec8a3320f.4.llvm.12847193204274187099+0x43]
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
mov    rax,QWORD PTR [rsp+0x8]
mov    BYTE PTR [rax+0x1],0x2
mov    cl,0x1
mov    BYTE PTR [rax],cl
add    rsp,0x98
pop    rbx
pop    r12
pop    r13
pop    r14
pop    r15
pop    rbp
ret
mov    rax,QWORD PTR [rsp+0x8]
mov    DWORD PTR [rax+0x4],r13d
mov    DWORD PTR [rax+0x8],r12d
mov    DWORD PTR [rax+0xc],ebx
mov    DWORD PTR [rax+0x10],ecx
xor    ecx,ecx
jmp    LOCAL+0x469
lea    rsi,[rdi+0x4]
lea    rcx,[RIP:anon.d47d9abe28adb0f891ea640ec8a3320f.6.llvm.12847193204274187099+0x18]
mov    edx,0x20
call   QWORD PTR [RIP:core::slice::index::slice_index_fail]
int3
int3
int3
int3
int3
int3

pv_dudect::kernels::entropy::seed_check @ 0x39950
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
