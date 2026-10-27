pv_dudect::main @ 0x2fef0
push   rbp
push   r15
push   r14
push   r13
push   r12
push   rbx
sub    rsp,0x3c8
lea    rbx,[rsp+0x3a8]
mov    rdi,rbx
call   QWORD PTR [RIP:std::env::args]
lea    rdi,[rsp+0x1f8]
mov    rsi,rbx
call   <alloc::vec::Vec<T> as alloc::vec::spec_from_iter_nested::SpecFromIterNested<T,I>>::from_iter
lea    rdx,[RIP:__frame_dummy_init_array_entry+0x2c0]
mov    esi,0x67
lea    rdi,[RIP:anon.cc9e1b464619ab62d021e6446458583c.8.llvm.15800808401943094617+0x54c]
cmp    QWORD PTR [rsp+0x208],0x3
jne    LOCAL+0x2e53
mov    rax,QWORD PTR [rsp+0x200]
cmp    QWORD PTR [rax+0x28],0x9
jne    LOCAL+0x2e53
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
jne    LOCAL+0x2e53
xor    rcx,QWORD PTR [r8]
movzx  edx,BYTE PTR [r8+0x8]
xor    rdx,0x6e
xor    ebx,ebx
or     rdx,rcx
setne  cl
mov    rsi,QWORD PTR [rax+0x38]
mov    rdi,QWORD PTR [rax+0x40]
cmp    rdi,0x1
je     LOCAL+0xd8
test   rdi,rdi
je     LOCAL+0x2e39
movzx  edx,BYTE PTR [rsi]
jmp    LOCAL+0xef
movzx  edx,BYTE PTR [rsi]
mov    al,0x1
cmp    edx,0x2b
je     LOCAL+0x2a09
cmp    edx,0x2d
je     LOCAL+0x2a09
xor    eax,eax
cmp    dl,0x2b
sete   al
mov    rdx,rdi
sub    rdx,rax
add    rsi,rax
neg    rax
cmp    rdx,0x11
jae    LOCAL+0x285
test   rdx,rdx
je     LOCAL+0x2e1e
add    rdi,rax
neg    rdi
xor    r9d,r9d
xor    eax,eax
data16 data16 data16 data16 data16 cs nop WORD PTR [rax+rax*1+0x0]
movzx  edx,BYTE PTR [rsi+r9*1]
add    edx,0xffffffd0
cmp    edx,0x9
ja     LOCAL+0x2d8c
lea    r8,[rax+rax*4]
mov    edx,edx
lea    rax,[rdx+r8*2]
inc    r9
mov    rdx,rdi
add    rdx,r9
jne    LOCAL+0x130
mov    bl,cl
test   ebx,ebx
mov    QWORD PTR [rsp+0x328],rax
je     LOCAL+0x2d7
cmp    rax,0xf4240
jne    LOCAL+0x2e1e
lea    rsi,[RIP:anon.cc9e1b464619ab62d021e6446458583c.8.llvm.15800808401943094617+0x3ea]
lea    rdi,[rsp+0x220]
mov    edx,0x32
call   QWORD PTR [RIP:std::fs::read::inner]
mov    r14,QWORD PTR [rsp+0x220]
movabs rax,0x8000000000000000
cmp    r14,rax
je     LOCAL+0x2c26
mov    r15,QWORD PTR [rsp+0x228]
mov    rax,QWORD PTR [rsp+0x230]
mov    QWORD PTR [rsp+0x90],r15
mov    QWORD PTR [rsp+0x98],rax
mov    QWORD PTR [rsp+0xa0],0x0
lea    rdi,[rsp+0x220]
lea    rsi,[rsp+0x90]
call   serde_json::de::from_trait
cmp    BYTE PTR [rsp+0x220],0x6
je     LOCAL+0x2c63
movupd xmm0,XMMWORD PTR [rsp+0x220]
movupd xmm1,XMMWORD PTR [rsp+0x230]
movapd XMMWORD PTR [rsp+0xa0],xmm1
movapd XMMWORD PTR [rsp+0x90],xmm0
test   r14,r14
je     LOCAL+0x232
mov    edx,0x1
mov    rdi,r15
mov    rsi,r14
call   QWORD PTR [RIP:__rustc::__rust_dealloc]
lea    rdi,[RIP:anon.cc9e1b464619ab62d021e6446458583c.8.llvm.15800808401943094617+0x59c]
lea    rdx,[rsp+0x90]
mov    esi,0x5
call   QWORD PTR [RIP:<str as serde_json::value::index::Index>::index_into]
test   rax,rax
jne    LOCAL+0x258
mov    rax,QWORD PTR [RIP:_DYNAMIC+0x260]
cmp    BYTE PTR [rax],0x2
jne    LOCAL+0x2ca0
mov    rcx,QWORD PTR [rax+0x8]
test   rcx,rcx
je     LOCAL+0x383
cmp    ecx,0x1
jne    LOCAL+0x3a5
xorps  xmm0,xmm0
cvtsi2sd xmm0,QWORD PTR [rax+0x10]
jmp    LOCAL+0x3aa
add    rdi,rax
neg    rdi
xor    r8d,r8d
mov    r9d,0xa
xor    eax,eax
cs nop WORD PTR [rax+rax*1+0x0]
mov    rdx,rdi
add    rdx,r8
je     LOCAL+0x156
mul    r9
movzx  edx,BYTE PTR [rsi+r8*1]
jo     LOCAL+0x29ff
add    edx,0xffffffd0
cmp    edx,0xa
jae    LOCAL+0x2d8c
mov    edx,edx
inc    r8
add    rax,rdx
jae    LOCAL+0x2a0
mov    al,0x2
jmp    LOCAL+0x2a09
cmp    rax,0x3e8
jne    LOCAL+0x2e1e
lea    rsi,[RIP:anon.cc9e1b464619ab62d021e6446458583c.8.llvm.15800808401943094617+0x3ea]
lea    rdi,[rsp+0x220]
mov    edx,0x32
call   QWORD PTR [RIP:std::sys::fs::metadata]
cmp    DWORD PTR [rsp+0x220],0x2
jne    LOCAL+0x2e40
mov    rax,QWORD PTR [rsp+0x228]
mov    ecx,eax
and    ecx,0x3
mov    QWORD PTR [rsp+0x1b8],0xffffffffffffffff
mov    r15d,0x7d0
cmp    ecx,0x1
jne    LOCAL+0x462
lea    r14,[rax-0x1]
mov    r15,QWORD PTR [rax-0x1]
mov    r12,QWORD PTR [rax+0x7]
mov    rax,QWORD PTR [r12]
test   rax,rax
je     LOCAL+0x34d
mov    rdi,r15
call   rax
mov    rsi,QWORD PTR [r12+0x8]
test   rsi,rsi
je     LOCAL+0x365
mov    rdx,QWORD PTR [r12+0x10]
mov    rdi,r15
call   QWORD PTR [RIP:__rustc::__rust_dealloc]
mov    esi,0x18
mov    edx,0x8
mov    rdi,r14
call   QWORD PTR [RIP:__rustc::__rust_dealloc]
mov    r15d,0x7d0
jmp    LOCAL+0x462
movsd  xmm1,QWORD PTR [rax+0x10]
unpcklps xmm1,XMMWORD PTR [RIP:GCC_except_table365+0xe4]
subpd  xmm1,XMMWORD PTR [RIP:GCC_except_table365+0x34]
movapd xmm0,xmm1
unpckhpd xmm0,xmm1
addsd  xmm0,xmm1
jmp    LOCAL+0x3aa
movsd  xmm0,QWORD PTR [rax+0x10]
call   QWORD PTR [RIP:floor]
cvttsd2si rax,xmm0
mov    rcx,rax
sar    rcx,0x3f
movapd xmm1,xmm0
subsd  xmm1,QWORD PTR [RIP:GCC_except_table365+0x524]
cvttsd2si rdx,xmm1
and    rdx,rcx
or     rdx,rax
xor    eax,eax
xorpd  xmm1,xmm1
ucomisd xmm0,xmm1
cmovae rax,rdx
ucomisd xmm0,QWORD PTR [RIP:GCC_except_table365+0x4d4]
mov    rcx,0xffffffffffffffff
cmovbe rcx,rax
mov    QWORD PTR [rsp+0x1b8],rcx
call   QWORD PTR [RIP:std::time::SystemTime::now]
mov    QWORD PTR [rsp+0x190],rax
mov    DWORD PTR [rsp+0x198],edx
lea    rdi,[rsp+0x220]
lea    rsi,[rsp+0x190]
xor    edx,edx
xor    ecx,ecx
call   QWORD PTR [RIP:std::time::SystemTime::duration_since]
cmp    DWORD PTR [rsp+0x220],0x1
je     LOCAL+0x2cbe
mov    rax,QWORD PTR [rsp+0x1b8]
cmp    QWORD PTR [rsp+0x228],rax
jae    LOCAL+0x2d00
lea    rdi,[rsp+0x90]
call   core::ptr::drop_in_place<serde_json::value::Value>
mov    r15d,0x1e8480
call   QWORD PTR [RIP:std::time::Instant::now]
lea    ecx,[r15*8+0x0]
mov    QWORD PTR [rsp+0x138],rcx
xor    ecx,ecx
test   ebx,ebx
mov    QWORD PTR [rsp+0x388],rax
mov    DWORD PTR [rsp+0x390],edx
mov    edx,0x2710
cmove  rdx,rcx
lea    rax,[RIP:anon.cc9e1b464619ab62d021e6446458583c.8.llvm.15800808401943094617+0x4ad]
lea    rcx,[RIP:anon.cc9e1b464619ab62d021e6446458583c.8.llvm.15800808401943094617+0x498]
cmove  rcx,rax
mov    QWORD PTR [rsp+0x318],rcx
mov    QWORD PTR [rsp+0xf8],rdx
lea    eax,[rdx*8+0x0]
mov    QWORD PTR [rsp+0x1c8],rax
mov    eax,ebx
lea    rax,[rax*4+0x11]
mov    QWORD PTR [rsp+0x320],rax
lea    rax,[r15-0x1]
mov    QWORD PTR [rsp+0x340],rax
movabs rbp,0x563337342d763200
lea    r14,[RIP:__frame_dummy_init_array_entry+0xf8]
mov    rcx,QWORD PTR [RIP:std::time::Instant::now]
lea    r12,[rsp+0x90]
xor    r13d,r13d
mov    DWORD PTR [rsp+0x1c4],ebx
mov    QWORD PTR [rsp+0x310],r15
lea    rax,[r14+r13*1]
mov    QWORD PTR [rsp+0x110],rax
call   rcx
mov    QWORD PTR [rsp+0x398],rax
mov    DWORD PTR [rsp+0x3a0],edx
xorpd  xmm0,xmm0
movapd XMMWORD PTR [rsp+0x300],xmm0
movapd XMMWORD PTR [rsp+0x2f0],xmm0
movapd XMMWORD PTR [rsp+0x2d0],xmm0
movapd XMMWORD PTR [rsp+0x2e0],xmm0
movapd XMMWORD PTR [rsp+0x370],xmm0
movapd XMMWORD PTR [rsp+0x360],xmm0
test   ebx,ebx
mov    QWORD PTR [rsp+0x1e0],r13
je     LOCAL+0x6c0
movabs rax,0x1b600000000
mov    QWORD PTR [rsp+0x90],rax
lea    rax,[rsp+0x98]
mov    WORD PTR [rax+0x4],0x0
mov    DWORD PTR [rax],0x0
mov    BYTE PTR [rsp+0x99],0x1
mov    BYTE PTR [rsp+0x9d],0x1
lea    rax,[rsp+0x110]
mov    QWORD PTR [rsp+0x220],rax
lea    rax,[RIP:<&T as core::fmt::Display>::fmt]
mov    QWORD PTR [rsp+0x228],rax
lea    rdi,[rsp+0x348]
lea    rsi,[RIP:anon.b180e950c2cf49b74b4bcf8edfb7f01a.3.llvm.1180291014484726119+0x6ea]
lea    rdx,[rsp+0x220]
call   QWORD PTR [RIP:alloc::fmt::format::format_inner]
mov    r14,QWORD PTR [rsp+0x350]
mov    rcx,QWORD PTR [rsp+0x358]
lea    rdi,[rsp+0x220]
mov    rsi,r12
mov    rdx,r14
call   QWORD PTR [RIP:std::fs::OpenOptions::_open]
mov    rsi,QWORD PTR [rsp+0x348]
test   rsi,rsi
je     LOCAL+0x62d
mov    edx,0x1
mov    rdi,r14
call   QWORD PTR [RIP:__rustc::__rust_dealloc]
cmp    DWORD PTR [rsp+0x220],0x1
je     LOCAL+0x2a3d
mov    r14,rbp
mov    ebp,DWORD PTR [rsp+0x224]
call   QWORD PTR [RIP:__rustc::__rust_no_alloc_shim_is_unstable_v2]
mov    edi,0x2000
mov    esi,0x1
call   QWORD PTR [RIP:__rustc::__rust_alloc]
test   rax,rax
je     LOCAL+0x2dfc
mov    QWORD PTR [rsp+0x118],0x2000
mov    QWORD PTR [rsp+0x120],rax
mov    BYTE PTR [rsp+0x130],0x0
mov    DWORD PTR [rsp+0x134],ebp
movups xmm0,XMMWORD PTR [RIP:DATA16:782c76616c69642c6f7574636f6d650a]
movups XMMWORD PTR [rax+0x1d],xmm0
movups xmm0,XMMWORD PTR [RIP:DATA16:72745f6175782c656e645f6175782c76]
movups XMMWORD PTR [rax+0x10],xmm0
movupd xmm0,XMMWORD PTR [RIP:anon.cc9e1b464619ab62d021e6446458583c.8.llvm.15800808401943094617+0x46b]
movupd XMMWORD PTR [rax],xmm0
mov    QWORD PTR [rsp+0x128],0x2d
mov    rbp,r14
jmp    LOCAL+0x6d2
nop    WORD PTR [rax+rax*1+0x0]
movabs rax,0x8000000000000000
mov    QWORD PTR [rsp+0x118],rax
call   QWORD PTR [RIP:__rustc::__rust_no_alloc_shim_is_unstable_v2]
mov    esi,0x8
mov    rdi,QWORD PTR [rsp+0x138]
call   QWORD PTR [RIP:__rustc::__rust_alloc]
test   rax,rax
je     LOCAL+0x2dd2
mov    r14,rax
add    QWORD PTR [rsp+0x1e0],0x10
xor    eax,eax
movdqa xmm0,XMMWORD PTR [RIP:DATA16:00000000000000000100000000000000]
movdqa xmm2,XMMWORD PTR [RIP:DATA16:01000000000000000100000000000000]
movdqa xmm3,XMMWORD PTR [RIP:DATA16:04000000000000000400000000000000]
nop    WORD PTR [rax+rax*1+0x0]
movdqa xmm1,xmm0
pand   xmm1,xmm2
movdqu XMMWORD PTR [r14+rax*8],xmm1
movdqu XMMWORD PTR [r14+rax*8+0x10],xmm1
add    rax,0x4
paddq  xmm0,xmm3
cmp    r15,rax
jne    LOCAL+0x720
mov    rcx,r15
data16 cs nop WORD PTR [rax+rax*1+0x0]
movabs rax,0x9e3779b97f4a7c15
add    rbp,rax
mov    rax,rbp
shr    rax,0x1e
xor    rax,rbp
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
div    rcx
cmp    rdx,QWORD PTR [rsp+0x340]
ja     LOCAL+0x2d3c
mov    rax,QWORD PTR [r14+rcx*8-0x8]
mov    rsi,QWORD PTR [r14+rdx*8]
mov    QWORD PTR [r14+rcx*8-0x8],rsi
dec    rcx
mov    QWORD PTR [r14+rdx*8],rax
cmp    rcx,0x1
ja     LOCAL+0x750
test   ebx,ebx
je     LOCAL+0x8f0
call   QWORD PTR [RIP:__rustc::__rust_no_alloc_shim_is_unstable_v2]
mov    esi,0x8
mov    rdi,QWORD PTR [rsp+0x1c8]
call   QWORD PTR [RIP:__rustc::__rust_alloc]
test   rax,rax
je     LOCAL+0x2de7
mov    rcx,rax
mov    eax,0x6
movdqa xmm0,XMMWORD PTR [RIP:DATA16:00000000000000000100000000000000]
movdqa xmm2,XMMWORD PTR [RIP:DATA16:01000000000000000100000000000000]
movdqa xmm3,XMMWORD PTR [RIP:DATA16:08000000000000000800000000000000]
nop
movdqa xmm1,xmm0
pand   xmm1,xmm2
movdqu XMMWORD PTR [rcx+rax*8-0x30],xmm1
movdqu XMMWORD PTR [rcx+rax*8-0x20],xmm1
movdqu XMMWORD PTR [rcx+rax*8-0x10],xmm1
movdqu XMMWORD PTR [rcx+rax*8],xmm1
paddq  xmm0,xmm3
add    rax,0x8
cmp    rax,0x2716
jne    LOCAL+0x810
mov    QWORD PTR [rsp+0x178],0x2710
mov    QWORD PTR [rsp+0x180],rcx
mov    QWORD PTR [rsp+0x188],0x2710
mov    esi,0x2710
data16 data16 cs nop WORD PTR [rax+rax*1+0x0]
movabs rax,0x9e3779b97f4a7c15
add    rbp,rax
mov    rax,rbp
shr    rax,0x1e
xor    rax,rbp
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
jae    LOCAL+0x2d6c
mov    rax,QWORD PTR [rcx+rsi*8-0x8]
mov    rdi,QWORD PTR [rcx+rdx*8]
mov    QWORD PTR [rcx+rsi*8-0x8],rdi
dec    rsi
mov    QWORD PTR [rcx+rdx*8],rax
cmp    rsi,0x1
ja     LOCAL+0x870
mov    rsi,QWORD PTR [rsp+0xf8]
jmp    LOCAL+0x916
xchg   ax,ax
mov    QWORD PTR [rsp+0x178],0x0
mov    QWORD PTR [rsp+0x180],0x8
mov    QWORD PTR [rsp+0x188],0x0
xor    esi,esi
mov    ecx,0x8
mov    r8d,0x8
lea    rdi,[rsp+0x178]
mov    rdx,r15
call   alloc::raw_vec::RawVecInner<A>::reserve::do_reserve_and_handle
mov    r12,r15
mov    rax,QWORD PTR [rsp+0x178]
mov    QWORD PTR [rsp+0x1d8],rax
mov    r13,QWORD PTR [rsp+0x180]
mov    rbx,QWORD PTR [rsp+0x188]
lea    rdi,[r13+rbx*8+0x0]
mov    rsi,r14
mov    r15,QWORD PTR [rsp+0x138]
mov    rdx,r15
call   QWORD PTR [RIP:memcpy@GLIBC_2.14]
add    rbx,r12
mov    QWORD PTR [rsp+0x188],rbx
mov    edx,0x8
mov    rdi,r14
mov    rsi,r15
call   QWORD PTR [RIP:__rustc::__rust_dealloc]
lea    rax,[rbx*8+0x0]
add    rax,r13
mov    QWORD PTR [rsp+0x338],rax
xor    r14d,r14d
mov    QWORD PTR [rsp+0x1d0],r13
jmp    LOCAL+0xb50
nop    DWORD PTR [rax+0x0]
mov    edx,0x4
mov    rdi,r14
mov    rsi,QWORD PTR [rsp+0x1e8]
call   QWORD PTR [RIP:__rustc::__rust_dealloc]
add    r13,0x8
mov    r14,QWORD PTR [rsp+0x108]
inc    r14
mov    esi,0x40
mov    edx,0x4
mov    rdi,rbp
call   QWORD PTR [RIP:__rustc::__rust_dealloc]
mov    BYTE PTR [rsp+0x18],0x0
mov    BYTE PTR [rsp+0x19],0x0
mov    BYTE PTR [rsp+0x1a],0x0
mov    BYTE PTR [rsp+0x1b],0x0
mov    BYTE PTR [rsp+0x1c],0x0
mov    BYTE PTR [rsp+0x1d],0x0
mov    BYTE PTR [rsp+0x1e],0x0
mov    BYTE PTR [rsp+0x1f],0x0
mov    BYTE PTR [rsp+0x20],0x0
mov    BYTE PTR [rsp+0x21],0x0
mov    BYTE PTR [rsp+0x22],0x0
mov    BYTE PTR [rsp+0x23],0x0
mov    BYTE PTR [rsp+0x24],0x0
mov    BYTE PTR [rsp+0x25],0x0
mov    BYTE PTR [rsp+0x26],0x0
mov    BYTE PTR [rsp+0x27],0x0
mov    BYTE PTR [rsp+0x28],0x0
mov    BYTE PTR [rsp+0x29],0x0
mov    BYTE PTR [rsp+0x2a],0x0
mov    BYTE PTR [rsp+0x2b],0x0
mov    BYTE PTR [rsp+0x2c],0x0
mov    BYTE PTR [rsp+0x2d],0x0
mov    BYTE PTR [rsp+0x2e],0x0
mov    BYTE PTR [rsp+0x2f],0x0
mov    BYTE PTR [rsp+0x30],0x0
mov    BYTE PTR [rsp+0x31],0x0
mov    BYTE PTR [rsp+0x32],0x0
mov    BYTE PTR [rsp+0x33],0x0
mov    BYTE PTR [rsp+0x34],0x0
mov    BYTE PTR [rsp+0x35],0x0
mov    BYTE PTR [rsp+0x36],0x0
mov    BYTE PTR [rsp+0x37],0x0
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
mov    BYTE PTR [rsp+0x50],0x0
mov    BYTE PTR [rsp+0x51],0x0
mov    BYTE PTR [rsp+0x52],0x0
mov    BYTE PTR [rsp+0x53],0x0
mov    BYTE PTR [rsp+0x54],0x0
mov    BYTE PTR [rsp+0x55],0x0
mov    BYTE PTR [rsp+0x56],0x0
mov    BYTE PTR [rsp+0x57],0x0
mov    BYTE PTR [rsp+0x58],0x0
mov    BYTE PTR [rsp+0x59],0x0
mov    BYTE PTR [rsp+0x5a],0x0
mov    BYTE PTR [rsp+0x5b],0x0
mov    BYTE PTR [rsp+0x5c],0x0
mov    BYTE PTR [rsp+0x5d],0x0
mov    BYTE PTR [rsp+0x5e],0x0
mov    BYTE PTR [rsp+0x5f],0x0
mov    QWORD PTR [rsp+0x38],0x0
mov    QWORD PTR [rsp+0x60],0x0
cmp    r13,QWORD PTR [rsp+0x338]
mov    rbp,QWORD PTR [rsp+0x148]
je     LOCAL+0x1f60
mov    rbx,QWORD PTR [r13+0x0]
mov    QWORD PTR [rsp+0x158],rbx
test   r14d,0x3ff
je     LOCAL+0xcd0
test   rbx,rbx
je     LOCAL+0xd2b
movq   xmm0,rbp
pshufd xmm2,xmm0,0x44
movdqa xmm3,xmm2
paddq  xmm3,XMMWORD PTR [RIP:GCC_except_table365+0x2e4]
paddq  xmm2,XMMWORD PTR [RIP:GCC_except_table365+0x2f4]
movabs rax,0x78dde6e5fd29f054
add    rbp,rax
movdqa xmm1,xmm2
psrlq  xmm1,0x1e
movdqa xmm0,xmm3
psrlq  xmm0,0x1e
pxor   xmm0,xmm3
pxor   xmm1,xmm2
movdqa xmm2,xmm1
movdqa xmm4,XMMWORD PTR [RIP:DATA16:6d4758bf000000006d4758bf00000000]
pmuludq xmm2,xmm4
movdqa xmm3,xmm1
psrlq  xmm3,0x20
movdqa xmm5,XMMWORD PTR [RIP:DATA16:b9e5e41c6d4758bfb9e5e41c6d4758bf]
pmuludq xmm3,xmm5
paddq  xmm3,xmm2
psllq  xmm3,0x20
pmuludq xmm1,xmm5
paddq  xmm1,xmm3
movdqa xmm2,xmm0
pmuludq xmm2,xmm4
movdqa xmm3,xmm0
psrlq  xmm3,0x20
pmuludq xmm3,xmm5
paddq  xmm3,xmm2
psllq  xmm3,0x20
pmuludq xmm0,xmm5
paddq  xmm0,xmm3
movdqa xmm3,xmm0
psrlq  xmm3,0x1b
movdqa xmm2,xmm1
psrlq  xmm2,0x1b
pxor   xmm2,xmm1
pxor   xmm3,xmm0
movdqa xmm0,xmm3
movdqa xmm4,XMMWORD PTR [RIP:DATA16:bb49d09400000000bb49d09400000000]
pmuludq xmm0,xmm4
movdqa xmm1,xmm3
psrlq  xmm1,0x20
movdqa xmm5,XMMWORD PTR [RIP:DATA16:eb113113bb49d094eb113113bb49d094]
pmuludq xmm1,xmm5
paddq  xmm1,xmm0
psllq  xmm1,0x20
pmuludq xmm3,xmm5
paddq  xmm3,xmm1
movdqa xmm0,xmm2
pmuludq xmm0,xmm4
movdqa xmm1,xmm2
psrlq  xmm1,0x20
pmuludq xmm1,xmm5
paddq  xmm1,xmm0
psllq  xmm1,0x20
pmuludq xmm2,xmm5
paddq  xmm2,xmm1
movdqa xmm0,xmm2
psrlq  xmm0,0x1f
movdqa xmm1,xmm3
psrlq  xmm1,0x1f
pxor   xmm1,xmm3
pxor   xmm0,xmm2
movdqa XMMWORD PTR [rsp+0x1a0],xmm0
movdqa XMMWORD PTR [rsp+0x190],xmm1
mov    rax,QWORD PTR [rsp+0x110]
jmp    LOCAL+0xd75
data16 data16 data16 data16 cs nop WORD PTR [rax+rax*1+0x0]
call   QWORD PTR [RIP:std::time::SystemTime::now]
mov    QWORD PTR [rsp+0x10],rax
mov    DWORD PTR [rsp+0x18],edx
lea    rdi,[rsp+0x220]
lea    rsi,[rsp+0x10]
xor    edx,edx
xor    ecx,ecx
call   QWORD PTR [RIP:std::time::SystemTime::duration_since]
cmp    DWORD PTR [rsp+0x220],0x1
je     LOCAL+0x2996
mov    rax,QWORD PTR [rsp+0x1b8]
cmp    QWORD PTR [rsp+0x228],rax
jae    LOCAL+0x29e1
mov    rbx,QWORD PTR [rsp+0x158]
test   rbx,rbx
jne    LOCAL+0xb72
mov    rax,QWORD PTR [rsp+0x110]
mov    rcx,QWORD PTR [rax+0x8]
cmp    rcx,0x5
jb     LOCAL+0xd5b
mov    rdx,QWORD PTR [rax]
mov    esi,DWORD PTR [rdx+rcx*1-0x5]
mov    edi,0x72657a2d
xor    esi,edi
movzx  ecx,BYTE PTR [rdx+rcx*1-0x1]
xor    ecx,0x6f
or     ecx,esi
je     LOCAL+0x1a94
movdqa xmm0,XMMWORD PTR [RIP:DATA16:35353535353535353535353535353535]
movdqa XMMWORD PTR [rsp+0x1a0],xmm0
movdqa XMMWORD PTR [rsp+0x190],xmm0
movdqa xmm0,XMMWORD PTR [rsp+0x190]
movdqa xmm1,XMMWORD PTR [rsp+0x1a0]
movdqa XMMWORD PTR [rsp+0x230],xmm1
movdqa XMMWORD PTR [rsp+0x220],xmm0
mov    rcx,QWORD PTR [rax+0x8]
cmp    rcx,0x7
mov    QWORD PTR [rsp+0x1f0],r13
jae    LOCAL+0xdf0
xor    eax,eax
movzx  edx,al
lea    rdi,[rsp+0x10]
lea    rsi,[rsp+0x220]
call   aspis_prover::state_only_hiding::prepare
test   rbx,rbx
jne    LOCAL+0xe35
mov    QWORD PTR [rsp+0x148],rbp
xor    ebx,ebx
mov    r13d,0x7
xor    r15d,r15d
xor    r12d,r12d
mov    DWORD PTR [rsp+0x140],0x7
jmp    LOCAL+0xfec
nop    DWORD PTR [rax]
mov    rax,QWORD PTR [rax]
mov    edx,DWORD PTR [rax+rcx*1-0x7]
mov    esi,0x6a65722d
xor    edx,esi
mov    eax,DWORD PTR [rax+rcx*1-0x4]
mov    ecx,0x7463656a
xor    eax,ecx
xor    ecx,ecx
or     eax,edx
sete   al
setne  dl
test   rbx,rbx
je     LOCAL+0xdad
mov    cl,dl
test   ecx,ecx
jne    LOCAL+0xdad
lea    rdi,[rsp+0x10]
lea    rsi,[rsp+0x220]
mov    edx,0x2
call   aspis_prover::state_only_hiding::prepare
movabs rax,0x9e3779b97f4a7c15
add    rax,rbp
mov    rcx,rax
shr    rcx,0x1e
xor    rcx,rax
movabs r8,0xbf58476d1ce4e5b9
imul   rcx,r8
mov    rax,rcx
shr    rax,0x1b
xor    rax,rcx
movabs r9,0x94d049bb133111eb
imul   rax,r9
mov    rsi,rax
shr    rsi,0x1f
xor    rsi,rax
mov    rax,rsi
shr    rax,1
movabs r10,0x8000000200000009
mul    r10
mov    rcx,rdx
shr    rcx,0x1d
lea    eax,[rcx+rcx*1]
shl    ecx,0x1f
add    ecx,eax
movabs rax,0x3c6ef372fe94f82a
add    rax,rbp
mov    rdx,rax
shr    rdx,0x1e
xor    rdx,rax
imul   rdx,r8
mov    rax,rdx
shr    rax,0x1b
xor    rax,rdx
imul   rax,r9
mov    rdi,rax
shr    rdi,0x1f
xor    rdi,rax
mov    rax,rdi
shr    rax,1
mul    r10
lea    eax,[rsi+rcx*1]
inc    eax
mov    DWORD PTR [rsp+0x140],eax
shr    rdx,0x1d
lea    eax,[rdx+rdx*1]
shl    edx,0x1f
add    edx,eax
lea    r13d,[rdi+rdx*1]
inc    r13d
movabs rax,0xdaa66d2c7ddf743f
add    rax,rbp
mov    rcx,rax
shr    rcx,0x1e
xor    rcx,rax
imul   rcx,r8
mov    rax,rcx
shr    rax,0x1b
xor    rax,rcx
imul   rax,r9
mov    rcx,rax
shr    rcx,0x1f
xor    rcx,rax
mov    rax,rcx
shr    rax,1
mul    r10
shr    rdx,0x1d
lea    eax,[rdx+rdx*1]
shl    edx,0x1f
add    edx,eax
lea    ebx,[rcx+rdx*1]
inc    ebx
movabs rax,0x78dde6e5fd29f054
add    rax,rbp
mov    rcx,rax
shr    rcx,0x1e
xor    rcx,rax
imul   rcx,r8
mov    rax,rcx
shr    rax,0x1b
xor    rax,rcx
imul   rax,r9
mov    rcx,rax
shr    rcx,0x1f
xor    rcx,rax
mov    rax,rcx
shr    rax,1
mul    r10
shr    rdx,0x1d
lea    eax,[rdx+rdx*1]
shl    edx,0x1f
add    edx,eax
lea    r15d,[rcx+rdx*1]
inc    r15d
movabs rax,0x1715609f7c746c69
add    rbp,rax
mov    rax,rbp
shr    rax,0x1e
mov    QWORD PTR [rsp+0x148],rbp
xor    rax,rbp
imul   rax,r8
mov    rcx,rax
shr    rcx,0x1b
xor    rcx,rax
imul   rcx,r9
mov    rsi,rcx
shr    rsi,0x1f
xor    rsi,rcx
mov    rax,rsi
shr    rax,1
mul    r10
shr    rdx,0x1d
lea    eax,[rdx+rdx*1]
shl    edx,0x1f
add    edx,eax
lea    r12d,[rsi+rdx*1]
inc    r12d
call   QWORD PTR [RIP:__rustc::__rust_no_alloc_shim_is_unstable_v2]
mov    edi,0x40
mov    esi,0x4
call   QWORD PTR [RIP:__rustc::__rust_alloc]
test   rax,rax
je     LOCAL+0x2d57
mov    rbp,rax
cmp    QWORD PTR [rsp+0x158],0x0
mov    QWORD PTR [rsp+0x108],r14
je     LOCAL+0x1560
movabs rax,0x9e3779b97f4a7c15
mov    r8,QWORD PTR [rsp+0x148]
add    rax,r8
mov    rcx,rax
shr    rcx,0x1e
xor    rcx,rax
movabs rsi,0xbf58476d1ce4e5b9
imul   rcx,rsi
mov    rax,rcx
shr    rax,0x1b
xor    rax,rcx
movabs rdi,0x94d049bb133111eb
imul   rax,rdi
mov    rcx,rax
shr    rcx,0x1f
xor    rcx,rax
mov    rax,rcx
shr    rax,1
movabs r9,0x8000000200000009
mul    r9
shr    rdx,0x1d
lea    eax,[rdx+rdx*1]
shl    edx,0x1f
add    edx,eax
lea    eax,[rcx+rdx*1]
inc    eax
mov    DWORD PTR [rbp+0x0],eax
movabs rax,0x3c6ef372fe94f82a
add    rax,r8
mov    rcx,rax
shr    rcx,0x1e
xor    rcx,rax
imul   rcx,rsi
mov    rax,rcx
shr    rax,0x1b
xor    rax,rcx
imul   rax,rdi
mov    rcx,rax
shr    rcx,0x1f
xor    rcx,rax
mov    rax,rcx
shr    rax,1
mul    r9
shr    rdx,0x1d
lea    eax,[rdx+rdx*1]
shl    edx,0x1f
add    edx,eax
lea    eax,[rcx+rdx*1]
inc    eax
mov    DWORD PTR [rbp+0x4],eax
movabs rax,0xdaa66d2c7ddf743f
add    rax,r8
mov    rcx,rax
shr    rcx,0x1e
xor    rcx,rax
imul   rcx,rsi
mov    rax,rcx
shr    rax,0x1b
xor    rax,rcx
imul   rax,rdi
mov    rcx,rax
shr    rcx,0x1f
xor    rcx,rax
mov    rax,rcx
shr    rax,1
mul    r9
shr    rdx,0x1d
lea    eax,[rdx+rdx*1]
shl    edx,0x1f
add    edx,eax
lea    eax,[rcx+rdx*1]
inc    eax
mov    DWORD PTR [rbp+0x8],eax
movabs rax,0x78dde6e5fd29f054
add    rax,r8
mov    rcx,rax
shr    rcx,0x1e
xor    rcx,rax
imul   rcx,rsi
mov    rax,rcx
shr    rax,0x1b
xor    rax,rcx
imul   rax,rdi
mov    rcx,rax
shr    rcx,0x1f
xor    rcx,rax
mov    rax,rcx
shr    rax,1
mul    r9
shr    rdx,0x1d
lea    eax,[rdx+rdx*1]
shl    edx,0x1f
add    edx,eax
lea    eax,[rcx+rdx*1]
inc    eax
mov    DWORD PTR [rbp+0xc],eax
movabs rax,0x1715609f7c746c69
add    rax,r8
mov    rcx,rax
shr    rcx,0x1e
xor    rcx,rax
imul   rcx,rsi
mov    rax,rcx
shr    rax,0x1b
xor    rax,rcx
imul   rax,rdi
mov    rcx,rax
shr    rcx,0x1f
xor    rcx,rax
mov    rax,rcx
shr    rax,1
mul    r9
shr    rdx,0x1d
lea    eax,[rdx+rdx*1]
shl    edx,0x1f
add    edx,eax
lea    eax,[rcx+rdx*1]
inc    eax
mov    DWORD PTR [rbp+0x10],eax
movabs rax,0xb54cda58fbbee87e
add    rax,r8
mov    rcx,rax
shr    rcx,0x1e
xor    rcx,rax
imul   rcx,rsi
mov    rax,rcx
shr    rax,0x1b
xor    rax,rcx
imul   rax,rdi
mov    rcx,rax
shr    rcx,0x1f
xor    rcx,rax
mov    rax,rcx
shr    rax,1
mul    r9
shr    rdx,0x1d
lea    eax,[rdx+rdx*1]
shl    edx,0x1f
add    edx,eax
lea    eax,[rcx+rdx*1]
inc    eax
mov    DWORD PTR [rbp+0x14],eax
movabs rax,0x538454127b096493
add    rax,r8
mov    rcx,rax
shr    rcx,0x1e
xor    rcx,rax
imul   rcx,rsi
mov    rax,rcx
shr    rax,0x1b
xor    rax,rcx
imul   rax,rdi
mov    rcx,rax
shr    rcx,0x1f
xor    rcx,rax
mov    rax,rcx
shr    rax,1
mul    r9
shr    rdx,0x1d
lea    eax,[rdx+rdx*1]
shl    edx,0x1f
add    edx,eax
lea    eax,[rcx+rdx*1]
inc    eax
mov    DWORD PTR [rbp+0x18],eax
movabs rax,0xf1bbcdcbfa53e0a8
add    rax,r8
mov    rcx,rax
shr    rcx,0x1e
xor    rcx,rax
imul   rcx,rsi
mov    rax,rcx
shr    rax,0x1b
xor    rax,rcx
imul   rax,rdi
mov    rcx,rax
shr    rcx,0x1f
xor    rcx,rax
mov    rax,rcx
shr    rax,1
mul    r9
shr    rdx,0x1d
lea    eax,[rdx+rdx*1]
shl    edx,0x1f
add    edx,eax
lea    eax,[rcx+rdx*1]
inc    eax
mov    DWORD PTR [rbp+0x1c],eax
movabs rax,0x8ff34785799e5cbd
add    rax,r8
mov    rcx,rax
shr    rcx,0x1e
xor    rcx,rax
imul   rcx,rsi
mov    rax,rcx
shr    rax,0x1b
xor    rax,rcx
imul   rax,rdi
mov    rcx,rax
shr    rcx,0x1f
xor    rcx,rax
mov    rax,rcx
shr    rax,1
mul    r9
shr    rdx,0x1d
lea    eax,[rdx+rdx*1]
shl    edx,0x1f
add    edx,eax
lea    eax,[rcx+rdx*1]
inc    eax
mov    DWORD PTR [rbp+0x20],eax
movabs rax,0x2e2ac13ef8e8d8d2
add    rax,r8
mov    rcx,rax
shr    rcx,0x1e
xor    rcx,rax
imul   rcx,rsi
mov    rax,rcx
shr    rax,0x1b
xor    rax,rcx
imul   rax,rdi
mov    rcx,rax
shr    rcx,0x1f
xor    rcx,rax
mov    rax,rcx
shr    rax,1
mul    r9
shr    rdx,0x1d
lea    eax,[rdx+rdx*1]
shl    edx,0x1f
add    edx,eax
lea    eax,[rcx+rdx*1]
inc    eax
mov    DWORD PTR [rbp+0x24],eax
movabs rax,0xcc623af8783354e7
add    rax,r8
mov    rcx,rax
shr    rcx,0x1e
xor    rcx,rax
imul   rcx,rsi
mov    rax,rcx
shr    rax,0x1b
xor    rax,rcx
imul   rax,rdi
mov    rcx,rax
shr    rcx,0x1f
xor    rcx,rax
mov    rax,rcx
shr    rax,1
mul    r9
shr    rdx,0x1d
lea    eax,[rdx+rdx*1]
shl    edx,0x1f
add    edx,eax
lea    eax,[rcx+rdx*1]
inc    eax
mov    DWORD PTR [rbp+0x28],eax
movabs rax,0x6a99b4b1f77dd0fc
add    rax,r8
mov    rcx,rax
shr    rcx,0x1e
xor    rcx,rax
imul   rcx,rsi
mov    rax,rcx
shr    rax,0x1b
xor    rax,rcx
imul   rax,rdi
mov    rcx,rax
shr    rcx,0x1f
xor    rcx,rax
mov    rax,rcx
shr    rax,1
mul    r9
shr    rdx,0x1d
lea    eax,[rdx+rdx*1]
shl    edx,0x1f
add    edx,eax
lea    eax,[rcx+rdx*1]
inc    eax
mov    DWORD PTR [rbp+0x2c],eax
movabs rax,0x8d12e6b76c84d11
add    rax,r8
mov    rcx,rax
shr    rcx,0x1e
xor    rcx,rax
imul   rcx,rsi
mov    rax,rcx
shr    rax,0x1b
xor    rax,rcx
imul   rax,rdi
mov    rcx,rax
shr    rcx,0x1f
xor    rcx,rax
mov    rax,rcx
shr    rax,1
mul    r9
shr    rdx,0x1d
lea    eax,[rdx+rdx*1]
shl    edx,0x1f
add    edx,eax
lea    eax,[rcx+rdx*1]
inc    eax
mov    DWORD PTR [rbp+0x30],eax
movabs rax,0xa708a824f612c926
add    rax,r8
mov    rcx,rax
shr    rcx,0x1e
xor    rcx,rax
imul   rcx,rsi
mov    rax,rcx
shr    rax,0x1b
xor    rax,rcx
imul   rax,rdi
mov    rcx,rax
shr    rcx,0x1f
xor    rcx,rax
mov    rax,rcx
shr    rax,1
mul    r9
shr    rdx,0x1d
lea    eax,[rdx+rdx*1]
shl    edx,0x1f
add    edx,eax
lea    eax,[rcx+rdx*1]
inc    eax
mov    DWORD PTR [rbp+0x34],eax
movabs rax,0x454021de755d453b
add    rax,r8
mov    rcx,rax
shr    rcx,0x1e
xor    rcx,rax
imul   rcx,rsi
mov    rax,rcx
shr    rax,0x1b
xor    rax,rcx
imul   rax,rdi
mov    rcx,rax
shr    rcx,0x1f
xor    rcx,rax
mov    rax,rcx
shr    rax,1
mul    r9
shr    rdx,0x1d
lea    eax,[rdx+rdx*1]
shl    edx,0x1f
add    edx,eax
lea    eax,[rcx+rdx*1]
inc    eax
mov    DWORD PTR [rbp+0x38],eax
movabs rax,0xe3779b97f4a7c150
add    r8,rax
mov    rax,r8
shr    rax,0x1e
mov    QWORD PTR [rsp+0x148],r8
xor    rax,r8
imul   rax,rsi
mov    rcx,rax
shr    rcx,0x1b
xor    rcx,rax
imul   rcx,rdi
mov    rsi,rcx
shr    rsi,0x1f
xor    rsi,rcx
mov    rax,rsi
shr    rax,1
mul    r9
shr    rdx,0x1d
lea    eax,[rdx+rdx*1]
shl    edx,0x1f
add    edx,eax
lea    eax,[rsi+rdx*1]
inc    eax
jmp    LOCAL+0x1591
data16 data16 data16 data16 cs nop WORD PTR [rax+rax*1+0x0]
movdqa xmm0,XMMWORD PTR [RIP:DATA16:07000000070000000700000007000000]
movdqu XMMWORD PTR [rbp+0x0],xmm0
movdqu XMMWORD PTR [rbp+0x10],xmm0
movdqu XMMWORD PTR [rbp+0x20],xmm0
movabs rax,0x700000007
mov    QWORD PTR [rbp+0x30],rax
mov    DWORD PTR [rbp+0x38],0x7
mov    eax,0x7
mov    DWORD PTR [rbp+0x3c],eax
mov    rax,QWORD PTR [rsp+0x110]
mov    cl,0x1
mov    DWORD PTR [rsp+0x104],ecx
mov    r14d,0x4
cmp    QWORD PTR [rax+0x8],0x4
jne    LOCAL+0x15c1
mov    rcx,QWORD PTR [rax]
cmp    DWORD PTR [rcx],0x656c6f70
je     LOCAL+0x16c5
xor    esi,esi
xor    edi,edi
pcmpeqd xmm0,xmm0
movdqa XMMWORD PTR [rsp+0x290],xmm0
movdqa XMMWORD PTR [rsp+0x280],xmm0
movdqa XMMWORD PTR [rsp+0x270],xmm0
movdqa XMMWORD PTR [rsp+0x260],xmm0
movdqa XMMWORD PTR [rsp+0x250],xmm0
movdqa XMMWORD PTR [rsp+0x240],xmm0
movdqa XMMWORD PTR [rsp+0x230],xmm0
movdqa XMMWORD PTR [rsp+0x220],xmm0
mov    rcx,QWORD PTR [rax+0x8]
add    rcx,0xfffffffffffffffc
cmp    rcx,0xc
mov    QWORD PTR [rsp+0x1e8],rdi
ja     LOCAL+0x1960
mov    rax,QWORD PTR [rax]
lea    rdx,[RIP:GCC_except_table365+0x55c]
movsxd rcx,DWORD PTR [rdx+rcx*4]
add    rcx,rdx
jmp    rcx
cmp    DWORD PTR [rax],0x656c6f70
jne    LOCAL+0x1960
mov    rax,QWORD PTR [rsp+0x108]
cmp    rax,QWORD PTR [rsp+0xf8]
jae    LOCAL+0x1bdb
mov    QWORD PTR [rsp+0x90],r14
mov    QWORD PTR [rsp+0x98],rsi
lea    r12,[rsp+0x90]
mov    rdi,QWORD PTR [rsp+0x90]
mov    rsi,QWORD PTR [rsp+0x98]
lea    rax,[rsp+0x220]
mov    QWORD PTR [rsp+0x90],rax
mov    rdx,QWORD PTR [rsp+0x90]
movdqu xmm0,XMMWORD PTR [RIP:DATA16:01000000000000000000000000000000]
movdqa XMMWORD PTR [rsp+0x90],xmm0
mov    rcx,r12
call   aspis_r1_cost_probe::ct_pole::all_slots_clear
mov    BYTE PTR [rsp+0x90],al
jmp    LOCAL+0x199e
call   QWORD PTR [RIP:__rustc::__rust_no_alloc_shim_is_unstable_v2]
mov    edi,0x10000
mov    esi,0x4
call   QWORD PTR [RIP:__rustc::__rust_alloc]
test   rax,rax
je     LOCAL+0x2daa
mov    r14,rax
mov    eax,0x3c
nop    DWORD PTR [rax+0x0]
mov    DWORD PTR [r14+rax*1-0x3c],r13d
mov    DWORD PTR [r14+rax*1-0x38],ebx
mov    DWORD PTR [r14+rax*1-0x34],r15d
mov    DWORD PTR [r14+rax*1-0x30],r12d
mov    DWORD PTR [r14+rax*1-0x2c],r13d
mov    DWORD PTR [r14+rax*1-0x28],ebx
mov    DWORD PTR [r14+rax*1-0x24],r15d
mov    DWORD PTR [r14+rax*1-0x20],r12d
mov    DWORD PTR [r14+rax*1-0x1c],r13d
mov    DWORD PTR [r14+rax*1-0x18],ebx
mov    DWORD PTR [r14+rax*1-0x14],r15d
mov    DWORD PTR [r14+rax*1-0x10],r12d
mov    DWORD PTR [r14+rax*1-0xc],r13d
mov    DWORD PTR [r14+rax*1-0x8],ebx
mov    DWORD PTR [r14+rax*1-0x4],r15d
mov    DWORD PTR [r14+rax*1],r12d
add    rax,0x40
cmp    rax,0x1003c
jne    LOCAL+0x16f0
mov    edi,0x10000
mov    esi,0x400
mov    rax,QWORD PTR [rsp+0x110]
mov    DWORD PTR [rsp+0x104],0x0
jmp    LOCAL+0x15c5
movabs rcx,0x31336d2d6b73616d
cmp    QWORD PTR [rax],rcx
je     LOCAL+0x1a4f
movabs rcx,0x766e692d31336d71
cmp    QWORD PTR [rax],rcx
je     LOCAL+0x1b7d
movabs rcx,0x73736572706d6f63
cmp    QWORD PTR [rax],rcx
jne    LOCAL+0x1960
mov    rax,QWORD PTR [rsp+0x108]
cmp    rax,QWORD PTR [rsp+0xf8]
jae    LOCAL+0x1d2d
mov    DWORD PTR [rsp+0x90],0x49
lea    r12,[rsp+0x90]
mov    esi,DWORD PTR [rsp+0x90]
mov    QWORD PTR [rsp+0x90],rbp
mov    QWORD PTR [rsp+0x98],0x10
mov    rdx,QWORD PTR [rsp+0x90]
mov    rcx,QWORD PTR [rsp+0x98]
movdqa xmm0,XMMWORD PTR [RIP:DATA16:0300000005000000070000000b000000]
movdqa XMMWORD PTR [rsp+0x90],xmm0
lea    rdi,[rsp+0x70]
mov    r8,r12
call   aspis_r1_cost_probe::prover_shared::compress_tagged_tuple
movdqu xmm0,XMMWORD PTR [rsp+0x70]
movdqa XMMWORD PTR [rsp+0x90],xmm0
jmp    LOCAL+0x199e
movdqu xmm0,XMMWORD PTR [rax]
pcmpeqb xmm0,XMMWORD PTR [RIP:GCC_except_table365+0x3a4]
pmovmskb eax,xmm0
cmp    eax,0xffff
jne    LOCAL+0x1960
jmp    LOCAL+0x18cc
mov    ecx,DWORD PTR [rax]
mov    edx,0x2d31336d
xor    ecx,edx
mov    eax,DWORD PTR [rax+0x3]
mov    edx,0x766e692d
xor    eax,edx
or     eax,ecx
jne    LOCAL+0x1960
mov    rax,QWORD PTR [rsp+0x108]
cmp    rax,QWORD PTR [rsp+0xf8]
jae    LOCAL+0x1c58
mov    eax,DWORD PTR [rsp+0x140]
mov    DWORD PTR [rsp+0x90],eax
lea    r12,[rsp+0x90]
mov    edi,DWORD PTR [rsp+0x90]
call   pv_dudect::inverse_m
mov    DWORD PTR [rsp+0x90],eax
jmp    LOCAL+0x199e
mov    rcx,QWORD PTR [rax]
movabs rdx,0x336d712d6b73616d
xor    rcx,rdx
movzx  eax,BYTE PTR [rax+0x8]
xor    rax,0x31
or     rax,rcx
jne    LOCAL+0x1960
mov    rax,QWORD PTR [rsp+0x108]
cmp    rax,QWORD PTR [rsp+0xf8]
jae    LOCAL+0x1a9d
lea    rax,[rsp+0x10]
mov    QWORD PTR [rsp+0x90],rax
lea    r12,[rsp+0x90]
mov    rsi,QWORD PTR [rsp+0x90]
mov    rdi,r12
call   aspis_prover::state_only_hiding::SeedExpander::qm31
mov    eax,DWORD PTR [rsp+0xa0]
mov    DWORD PTR [rsp+0x80],eax
movdqu xmm0,XMMWORD PTR [rsp+0x90]
movdqa XMMWORD PTR [rsp+0x70],xmm0
lea    rax,[rsp+0x70]
jmp    LOCAL+0x199e
mov    rcx,QWORD PTR [rax]
movabs rdx,0x31336d2d6b73616d
xor    rcx,rdx
mov    rax,QWORD PTR [rax+0x7]
movabs rdx,0x7463656a65722d31
xor    rax,rdx
or     rax,rcx
je     LOCAL+0x1a4f
data16 cs nop WORD PTR [rax+rax*1+0x0]
mov    rax,QWORD PTR [rsp+0x108]
cmp    rax,QWORD PTR [rsp+0xf8]
jae    LOCAL+0x19f0
lea    rax,[rsp+0x190]
mov    QWORD PTR [rsp+0x90],rax
lea    r12,[rsp+0x90]
mov    rdi,QWORD PTR [rsp+0x90]
call   aspis_prover::state_only_entropy::seed_check
mov    BYTE PTR [rsp+0x90],al
mov    BYTE PTR [rsp+0xe],0x1
mov    QWORD PTR [rsp+0x210],0x0
mov    DWORD PTR [rsp+0x150],0x0
mov    DWORD PTR [rsp+0x154],0x0
mov    BYTE PTR [rsp+0xf],0x1
cmp    BYTE PTR [rsp+0x104],0x0
mov    r13,QWORD PTR [rsp+0x1f0]
je     LOCAL+0x9b0
jmp    LOCAL+0x9c6
data16 cs nop WORD PTR [rax+rax*1+0x0]
lfence
rdtscp
mov    r13,rax
mov    r12d,ecx
mov    rbx,rdx
lfence
lea    rax,[rsp+0x190]
mov    QWORD PTR [rsp+0x90],rax
lea    rax,[rsp+0x90]
mov    rdi,QWORD PTR [rsp+0x90]
call   aspis_prover::state_only_entropy::seed_check
shl    rbx,0x20
or     r13,rbx
mov    BYTE PTR [rsp+0xe],al
lea    rax,[rsp+0xe]
lfence
rdtscp
shl    rdx,0x20
or     rdx,rax
lfence
sub    rdx,r13
jmp    LOCAL+0x1dd0
mov    rax,QWORD PTR [rsp+0x108]
cmp    rax,QWORD PTR [rsp+0xf8]
jae    LOCAL+0x1b14
lea    rax,[rsp+0x10]
mov    QWORD PTR [rsp+0x90],rax
lea    r12,[rsp+0x90]
mov    rdi,QWORD PTR [rsp+0x90]
call   aspis_prover::state_only_hiding::SeedExpander::m31
mov    QWORD PTR [rsp+0x90],rax
jmp    LOCAL+0x199e
pxor   xmm0,xmm0
jmp    LOCAL+0xd63
lfence
rdtscp
mov    r13,rax
mov    r12d,ecx
mov    rbx,rdx
lfence
lea    rax,[rsp+0x10]
mov    QWORD PTR [rsp+0x90],rax
lea    rdi,[rsp+0x90]
mov    rsi,QWORD PTR [rsp+0x90]
call   aspis_prover::state_only_hiding::SeedExpander::qm31
shl    rbx,0x20
or     r13,rbx
mov    eax,DWORD PTR [rsp+0xa0]
mov    DWORD PTR [rsp+0x80],eax
movdqu xmm0,XMMWORD PTR [rsp+0x90]
movdqa XMMWORD PTR [rsp+0x70],xmm0
lea    rax,[rsp+0x70]
lfence
rdtscp
shl    rdx,0x20
or     rdx,rax
lfence
sub    rdx,r13
movzx  eax,BYTE PTR [rsp+0x70]
jmp    LOCAL+0x1b72
lfence
rdtscp
mov    r13,rax
mov    r12d,ecx
mov    rbx,rdx
lfence
lea    rax,[rsp+0x10]
mov    QWORD PTR [rsp+0x90],rax
lea    r15,[rsp+0x90]
mov    rdi,QWORD PTR [rsp+0x90]
call   aspis_prover::state_only_hiding::SeedExpander::m31
shl    rbx,0x20
or     r13,rbx
mov    QWORD PTR [rsp+0x90],rax
lfence
rdtscp
shl    rdx,0x20
or     rdx,rax
lfence
sub    rdx,r13
movzx  eax,BYTE PTR [rsp+0x90]
xor    al,0x1
mov    BYTE PTR [rsp+0xe],al
jmp    LOCAL+0x1dd0
mov    rax,QWORD PTR [rsp+0x108]
cmp    rax,QWORD PTR [rsp+0xf8]
jae    LOCAL+0x1c9f
mov    DWORD PTR [rsp+0x90],r13d
mov    DWORD PTR [rsp+0x94],ebx
mov    DWORD PTR [rsp+0x98],r15d
mov    DWORD PTR [rsp+0x9c],r12d
lea    r12,[rsp+0x90]
lea    rdi,[rsp+0x70]
mov    rsi,r12
call   pv_dudect::inverse_q
movdqu xmm0,XMMWORD PTR [rsp+0x70]
movdqa XMMWORD PTR [rsp+0x90],xmm0
jmp    LOCAL+0x199e
lfence
rdtscp
mov    r13,rax
mov    r12d,ecx
mov    rbx,rdx
lfence
mov    QWORD PTR [rsp+0x90],r14
mov    QWORD PTR [rsp+0x98],rsi
lea    rcx,[rsp+0x90]
mov    rdi,QWORD PTR [rsp+0x90]
mov    rsi,QWORD PTR [rsp+0x98]
lea    rax,[rsp+0x220]
mov    QWORD PTR [rsp+0x90],rax
mov    rdx,QWORD PTR [rsp+0x90]
movdqu xmm0,XMMWORD PTR [RIP:DATA16:01000000000000000000000000000000]
movdqa XMMWORD PTR [rsp+0x90],xmm0
call   aspis_r1_cost_probe::ct_pole::all_slots_clear
shl    rbx,0x20
or     r13,rbx
mov    BYTE PTR [rsp+0xe],al
lea    rax,[rsp+0xe]
jmp    LOCAL+0x1a37
lfence
rdtscp
mov    r13,rax
mov    r12d,ecx
mov    rbx,rdx
lfence
mov    eax,DWORD PTR [rsp+0x140]
mov    DWORD PTR [rsp+0x90],eax
lea    r15,[rsp+0x90]
mov    edi,DWORD PTR [rsp+0x90]
call   pv_dudect::inverse_m
shl    rbx,0x20
or     r13,rbx
mov    DWORD PTR [rsp+0x90],eax
jmp    LOCAL+0x1db1
lfence
rdtscp
mov    QWORD PTR [rsp+0x140],rax
mov    QWORD PTR [rsp+0x330],rdx
lfence
mov    DWORD PTR [rsp+0x90],r13d
mov    DWORD PTR [rsp+0x94],ebx
mov    DWORD PTR [rsp+0x98],r15d
mov    DWORD PTR [rsp+0x9c],r12d
mov    r12d,ecx
lea    rbx,[rsp+0x90]
lea    rdi,[rsp+0x70]
mov    rsi,rbx
call   pv_dudect::inverse_q
mov    rax,QWORD PTR [rsp+0x330]
shl    rax,0x20
mov    rsi,QWORD PTR [rsp+0x140]
or     rsi,rax
movdqu xmm0,XMMWORD PTR [rsp+0x70]
movdqa XMMWORD PTR [rsp+0x90],xmm0
lfence
rdtscp
shl    rdx,0x20
lfence
or     rdx,rax
sub    rdx,rsi
jmp    LOCAL+0x1dc4
lfence
rdtscp
mov    r13,rax
mov    r12d,ecx
mov    rbx,rdx
lfence
mov    DWORD PTR [rsp+0x90],0x49
lea    r15,[rsp+0x90]
mov    esi,DWORD PTR [rsp+0x90]
mov    QWORD PTR [rsp+0x90],rbp
mov    QWORD PTR [rsp+0x98],0x10
mov    rdx,QWORD PTR [rsp+0x90]
mov    rcx,QWORD PTR [rsp+0x98]
movdqa xmm0,XMMWORD PTR [RIP:DATA16:0300000005000000070000000b000000]
movdqa XMMWORD PTR [rsp+0x90],xmm0
lea    rdi,[rsp+0x70]
mov    r8,r15
call   aspis_r1_cost_probe::prover_shared::compress_tagged_tuple
shl    rbx,0x20
or     r13,rbx
movdqu xmm0,XMMWORD PTR [rsp+0x70]
movdqa XMMWORD PTR [rsp+0x90],xmm0
lfence
rdtscp
shl    rdx,0x20
lfence
or     rdx,rax
sub    rdx,r13
mov    BYTE PTR [rsp+0xe],0x1
nop    DWORD PTR [rax+0x0]
mov    QWORD PTR [rsp+0x210],rdx
mov    DWORD PTR [rsp+0x150],r12d
mov    DWORD PTR [rsp+0x154],ecx
movzx  esi,BYTE PTR [rsp+0xe]
mov    BYTE PTR [rsp+0xf],sil
mov    rdi,QWORD PTR [rsp+0x158]
cmp    rdi,0x2
jae    LOCAL+0x2d93
mov    rax,rdi
shl    rax,0x4
lea    r8,[rsp+rax*1]
add    r8,0x360
inc    QWORD PTR [r8+rsi*8]
lea    rsi,[rsp+0x2e0]
cmp    r12d,ecx
sete   BYTE PTR [rsp+0x8f]
lea    r12,[rsp+0x90]
mov    r13,QWORD PTR [rsp+0x1f0]
jne    LOCAL+0x1e57
add    QWORD PTR [rsp+rax*1+0x2f0],rdx
adc    QWORD PTR [rsp+rax*1+0x2f8],0x0
lea    rsi,[rsp+0x2d0]
inc    QWORD PTR [rsi+rdi*8]
movabs rax,0x8000000000000000
cmp    QWORD PTR [rsp+0x118],rax
je     LOCAL+0x1f44
lea    rax,[rsp+0x158]
mov    QWORD PTR [rsp+0x90],rax
mov    rax,QWORD PTR [RIP:core::fmt::num::imp::<impl core::fmt::Display for u64>::fmt]
mov    QWORD PTR [rsp+0x98],rax
lea    rax,[rsp+0x210]
mov    QWORD PTR [rsp+0xa0],rax
mov    rax,QWORD PTR [RIP:core::fmt::num::imp::<impl core::fmt::Display for u64>::fmt]
mov    QWORD PTR [rsp+0xa8],rax
lea    rax,[rsp+0x150]
mov    QWORD PTR [rsp+0xb0],rax
mov    rax,QWORD PTR [RIP:core::fmt::num::imp::<impl core::fmt::Display for u32>::fmt]
mov    QWORD PTR [rsp+0xb8],rax
lea    rcx,[rsp+0x154]
mov    QWORD PTR [rsp+0xc0],rcx
mov    QWORD PTR [rsp+0xc8],rax
lea    rax,[rsp+0x8f]
mov    QWORD PTR [rsp+0xd0],rax
mov    rax,QWORD PTR [RIP:<bool as core::fmt::Display>::fmt]
mov    QWORD PTR [rsp+0xd8],rax
lea    rcx,[rsp+0xf]
mov    QWORD PTR [rsp+0xe0],rcx
mov    QWORD PTR [rsp+0xe8],rax
lea    rdi,[rsp+0x118]
lea    rsi,[RIP:anon.4227ec7036ba7d8315078e57be449868.0.llvm.13362339970539153419+0x211]
mov    rdx,r12
call   std::io::default_write_fmt
test   rax,rax
jne    LOCAL+0x2967
lea    r12,[rsp+0x90]
cmp    BYTE PTR [rsp+0x104],0x0
je     LOCAL+0x9b0
jmp    LOCAL+0x9c6
nop    WORD PTR [rax+rax*1+0x0]
mov    rsi,QWORD PTR [rsp+0x1d8]
test   rsi,rsi
je     LOCAL+0x1f84
shl    rsi,0x3
mov    edx,0x8
mov    rdi,QWORD PTR [rsp+0x1d0]
call   QWORD PTR [RIP:__rustc::__rust_dealloc]
movabs rax,0x8000000000000000
cmp    QWORD PTR [rsp+0x118],rax
je     LOCAL+0x1fae
lea    rdi,[rsp+0x118]
call   std::io::buffered::bufwriter::BufWriter<W>::flush_buf
test   rax,rax
jne    LOCAL+0x2a74
mov    QWORD PTR [rsp+0x160],0x0
mov    QWORD PTR [rsp+0x170],0x0
call   QWORD PTR [RIP:__rustc::__rust_no_alloc_shim_is_unstable_v2]
mov    r15d,0x6
mov    edi,0x6
mov    esi,0x1
call   QWORD PTR [RIP:__rustc::__rust_alloc]
test   rax,rax
je     LOCAL+0x2dbf
mov    r14,rax
mov    WORD PTR [rax+0x4],0x796c
mov    DWORD PTR [rax],0x696d6166
mov    QWORD PTR [rsp+0x70],0x6
mov    QWORD PTR [rsp+0x78],rax
mov    QWORD PTR [rsp+0x80],0x6
mov    rax,QWORD PTR [rsp+0x110]
mov    r15,QWORD PTR [rax+0x8]
test   r15,r15
js     LOCAL+0x28ef
mov    rbx,QWORD PTR [rax]
je     LOCAL+0x205e
call   QWORD PTR [RIP:__rustc::__rust_no_alloc_shim_is_unstable_v2]
mov    r13d,0x1
mov    esi,0x1
mov    rdi,r15
call   QWORD PTR [RIP:__rustc::__rust_alloc]
test   rax,rax
je     LOCAL+0x28f2
mov    rbp,rax
lea    r12,[rsp+0x90]
jmp    LOCAL+0x2063
mov    ebp,0x1
mov    rdi,rbp
mov    rsi,rbx
mov    rdx,r15
call   QWORD PTR [RIP:memcpy@GLIBC_2.14]
mov    BYTE PTR [rsp+0x90],0x3
mov    QWORD PTR [rsp+0x98],r15
mov    QWORD PTR [rsp+0xa0],rbp
mov    QWORD PTR [rsp+0xa8],r15
lea    rdi,[rsp+0x10]
lea    rsi,[rsp+0x160]
lea    rdx,[rsp+0x70]
mov    rcx,r12
call   alloc::collections::btree::map::BTreeMap<K,V,A>::insert
cmp    BYTE PTR [rsp+0x10],0x6
mov    rbp,QWORD PTR [rsp+0x148]
je     LOCAL+0x20c5
lea    rdi,[rsp+0x10]
call   core::ptr::drop_in_place<serde_json::value::Value>
call   QWORD PTR [RIP:__rustc::__rust_no_alloc_shim_is_unstable_v2]
mov    r15d,0x5
mov    edi,0x5
mov    esi,0x1
call   QWORD PTR [RIP:__rustc::__rust_alloc]
test   rax,rax
je     LOCAL+0x2dbf
mov    r14,rax
mov    BYTE PTR [rax+0x4],0x6c
mov    DWORD PTR [rax],0x6562616c
mov    QWORD PTR [rsp+0x70],0x5
mov    QWORD PTR [rsp+0x78],rax
mov    QWORD PTR [rsp+0x80],0x5
call   QWORD PTR [RIP:__rustc::__rust_no_alloc_shim_is_unstable_v2]
mov    esi,0x1
mov    r15,QWORD PTR [rsp+0x320]
mov    rdi,r15
call   QWORD PTR [RIP:__rustc::__rust_alloc]
test   rax,rax
je     LOCAL+0x2e0e
mov    rbx,rax
mov    rdi,rax
mov    rsi,QWORD PTR [rsp+0x318]
mov    rdx,r15
call   QWORD PTR [RIP:memcpy@GLIBC_2.14]
mov    BYTE PTR [rsp+0x90],0x3
mov    QWORD PTR [rsp+0x98],r15
mov    QWORD PTR [rsp+0xa0],rbx
mov    QWORD PTR [rsp+0xa8],r15
lea    rdi,[rsp+0x10]
lea    rsi,[rsp+0x160]
lea    rdx,[rsp+0x70]
mov    rcx,r12
call   alloc::collections::btree::map::BTreeMap<K,V,A>::insert
cmp    BYTE PTR [rsp+0x10],0x6
mov    ebx,DWORD PTR [rsp+0x1c4]
je     LOCAL+0x219f
lea    rdi,[rsp+0x10]
call   core::ptr::drop_in_place<serde_json::value::Value>
call   QWORD PTR [RIP:__rustc::__rust_no_alloc_shim_is_unstable_v2]
mov    r15d,0x9
mov    edi,0x9
mov    esi,0x1
call   QWORD PTR [RIP:__rustc::__rust_alloc]
test   rax,rax
je     LOCAL+0x2dbf
movabs rcx,0x73616c635f726570
mov    QWORD PTR [rax],rcx
mov    BYTE PTR [rax+0x8],0x73
mov    QWORD PTR [rsp+0x70],0x9
mov    QWORD PTR [rsp+0x78],rax
mov    QWORD PTR [rsp+0x80],0x9
mov    BYTE PTR [rsp+0x90],0x2
mov    QWORD PTR [rsp+0x98],0x0
mov    rax,QWORD PTR [rsp+0x328]
mov    QWORD PTR [rsp+0xa0],rax
lea    rdi,[rsp+0x10]
lea    rsi,[rsp+0x160]
lea    rdx,[rsp+0x70]
mov    rcx,r12
call   alloc::collections::btree::map::BTreeMap<K,V,A>::insert
cmp    BYTE PTR [rsp+0x10],0x6
je     LOCAL+0x223e
lea    rdi,[rsp+0x10]
call   core::ptr::drop_in_place<serde_json::value::Value>
call   QWORD PTR [RIP:__rustc::__rust_no_alloc_shim_is_unstable_v2]
mov    r15d,0x5
mov    edi,0x5
mov    esi,0x1
call   QWORD PTR [RIP:__rustc::__rust_alloc]
test   rax,rax
je     LOCAL+0x2dbf
mov    r14,rax
mov    BYTE PTR [rax+0x4],0x64
mov    DWORD PTR [rax],0x696c6176
mov    QWORD PTR [rsp+0x70],0x5
mov    QWORD PTR [rsp+0x78],rax
mov    QWORD PTR [rsp+0x80],0x5
mov    rdi,r12
lea    rsi,[rsp+0x2d0]
call   serde_json::value::to_value
cmp    BYTE PTR [rsp+0x90],0x6
je     LOCAL+0x2aa9
movdqu xmm0,XMMWORD PTR [rsp+0x90]
movdqu xmm1,XMMWORD PTR [rsp+0xa0]
movdqa XMMWORD PTR [rsp+0x20],xmm1
movdqa XMMWORD PTR [rsp+0x10],xmm0
mov    rdi,r12
lea    rsi,[rsp+0x160]
lea    rdx,[rsp+0x70]
lea    rcx,[rsp+0x10]
call   alloc::collections::btree::map::BTreeMap<K,V,A>::insert
cmp    BYTE PTR [rsp+0x90],0x6
je     LOCAL+0x22f2
mov    rdi,r12
call   core::ptr::drop_in_place<serde_json::value::Value>
call   QWORD PTR [RIP:__rustc::__rust_no_alloc_shim_is_unstable_v2]
mov    r15d,0xa
mov    edi,0xa
mov    esi,0x1
call   QWORD PTR [RIP:__rustc::__rust_alloc]
test   rax,rax
je     LOCAL+0x2dbf
mov    r14,rax
movabs rax,0x6f6974617267696d
mov    QWORD PTR [r14],rax
mov    WORD PTR [r14+0x8],0x736e
mov    QWORD PTR [rsp+0x70],0xa
mov    QWORD PTR [rsp+0x78],r14
mov    QWORD PTR [rsp+0x80],0xa
mov    rdi,r12
lea    rsi,[rsp+0x2e0]
call   serde_json::value::to_value
cmp    BYTE PTR [rsp+0x90],0x6
je     LOCAL+0x2ae0
movdqu xmm0,XMMWORD PTR [rsp+0x90]
movdqu xmm1,XMMWORD PTR [rsp+0xa0]
movdqa XMMWORD PTR [rsp+0x20],xmm1
movdqa XMMWORD PTR [rsp+0x10],xmm0
mov    rdi,r12
lea    rsi,[rsp+0x160]
lea    rdx,[rsp+0x70]
lea    rcx,[rsp+0x10]
call   alloc::collections::btree::map::BTreeMap<K,V,A>::insert
cmp    BYTE PTR [rsp+0x90],0x6
je     LOCAL+0x23b0
mov    rdi,r12
call   core::ptr::drop_in_place<serde_json::value::Value>
call   QWORD PTR [RIP:__rustc::__rust_no_alloc_shim_is_unstable_v2]
mov    r15d,0x13
mov    edi,0x13
mov    esi,0x1
call   QWORD PTR [RIP:__rustc::__rust_alloc]
test   rax,rax
je     LOCAL+0x2dbf
mov    r14,rax
movups xmm0,XMMWORD PTR [RIP:DATA16:6f7574636f6d65735f66616c73655f74]
movups XMMWORD PTR [rax],xmm0
mov    DWORD PTR [rax+0xf],0x65757274
mov    QWORD PTR [rsp+0x70],0x13
mov    QWORD PTR [rsp+0x78],rax
mov    QWORD PTR [rsp+0x80],0x13
mov    rdi,r12
lea    rsi,[rsp+0x360]
call   serde_json::value::to_value
cmp    BYTE PTR [rsp+0x90],0x6
je     LOCAL+0x2b17
movupd xmm0,XMMWORD PTR [rsp+0x90]
movdqu xmm1,XMMWORD PTR [rsp+0xa0]
movdqa XMMWORD PTR [rsp+0x20],xmm1
movapd XMMWORD PTR [rsp+0x10],xmm0
mov    rdi,r12
lea    rsi,[rsp+0x160]
lea    rdx,[rsp+0x70]
lea    rcx,[rsp+0x10]
call   alloc::collections::btree::map::BTreeMap<K,V,A>::insert
cmp    BYTE PTR [rsp+0x90],0x6
je     LOCAL+0x246b
mov    rdi,r12
call   core::ptr::drop_in_place<serde_json::value::Value>
call   QWORD PTR [RIP:__rustc::__rust_no_alloc_shim_is_unstable_v2]
mov    r15d,0xb
mov    edi,0xb
mov    esi,0x1
call   QWORD PTR [RIP:__rustc::__rust_alloc]
test   rax,rax
je     LOCAL+0x2dbf
mov    r14,rax
movabs rax,0x6379635f6e61656d
mov    QWORD PTR [r14],rax
mov    DWORD PTR [r14+0x7],0x73656c63
mov    QWORD PTR [rsp+0x70],0xb
mov    QWORD PTR [rsp+0x78],r14
mov    QWORD PTR [rsp+0x80],0xb
call   QWORD PTR [RIP:__rustc::__rust_no_alloc_shim_is_unstable_v2]
mov    edi,0x40
mov    esi,0x8
call   QWORD PTR [RIP:__rustc::__rust_alloc]
test   rax,rax
je     LOCAL+0x2b4e
mov    r15,rax
mov    rdi,QWORD PTR [rsp+0x2f0]
mov    rsi,QWORD PTR [rsp+0x2f8]
call   QWORD PTR [RIP:__floatuntidf]
movsd  xmm1,QWORD PTR [rsp+0x2d0]
unpcklps xmm1,XMMWORD PTR [RIP:GCC_except_table365+0xe4]
subpd  xmm1,XMMWORD PTR [RIP:GCC_except_table365+0x34]
movapd xmm2,xmm1
unpckhpd xmm2,xmm1
addsd  xmm2,xmm1
divsd  xmm0,xmm2
mov    rdi,r12
call   QWORD PTR [RIP:serde_json::value::from::<impl core::convert::From<f64> for serde_json::value::Value>::from]
cmp    BYTE PTR [rsp+0x90],0x6
je     LOCAL+0x2b63
movupd xmm0,XMMWORD PTR [rsp+0x90]
movups xmm1,XMMWORD PTR [rsp+0xa0]
movaps XMMWORD PTR [rsp+0x20],xmm1
movapd XMMWORD PTR [rsp+0x10],xmm0
mov    rdi,QWORD PTR [rsp+0x300]
mov    rsi,QWORD PTR [rsp+0x308]
call   QWORD PTR [RIP:__floatuntidf]
movsd  xmm1,QWORD PTR [rsp+0x2d8]
unpcklps xmm1,XMMWORD PTR [RIP:GCC_except_table365+0xe4]
subpd  xmm1,XMMWORD PTR [RIP:GCC_except_table365+0x34]
movapd xmm2,xmm1
unpckhpd xmm2,xmm1
addsd  xmm2,xmm1
divsd  xmm0,xmm2
mov    rdi,r12
call   QWORD PTR [RIP:serde_json::value::from::<impl core::convert::From<f64> for serde_json::value::Value>::from]
cmp    BYTE PTR [rsp+0x90],0x6
je     LOCAL+0x2b9a
movups xmm0,XMMWORD PTR [rsp+0x90]
movups xmm1,XMMWORD PTR [rsp+0xa0]
movups XMMWORD PTR [r15+0x30],xmm1
movups XMMWORD PTR [r15+0x20],xmm0
movapd xmm0,XMMWORD PTR [rsp+0x10]
movapd xmm1,XMMWORD PTR [rsp+0x20]
movupd XMMWORD PTR [r15+0x10],xmm1
movupd XMMWORD PTR [r15],xmm0
mov    QWORD PTR [rsp+0x98],0x2
mov    QWORD PTR [rsp+0xa0],r15
mov    QWORD PTR [rsp+0xa8],0x2
mov    BYTE PTR [rsp+0x90],0x4
lea    rdi,[rsp+0x10]
lea    rsi,[rsp+0x160]
lea    rdx,[rsp+0x70]
mov    rcx,r12
call   alloc::collections::btree::map::BTreeMap<K,V,A>::insert
cmp    BYTE PTR [rsp+0x10],0x6
je     LOCAL+0x262e
lea    rdi,[rsp+0x10]
call   core::ptr::drop_in_place<serde_json::value::Value>
call   QWORD PTR [RIP:__rustc::__rust_no_alloc_shim_is_unstable_v2]
mov    r15d,0xc
mov    edi,0xc
mov    esi,0x1
call   QWORD PTR [RIP:__rustc::__rust_alloc]
test   rax,rax
je     LOCAL+0x2dbf
mov    r14,rax
movabs rax,0x6365735f6c6c6177
mov    QWORD PTR [r14],rax
mov    DWORD PTR [r14+0x8],0x73646e6f
mov    QWORD PTR [rsp+0x70],0xc
mov    QWORD PTR [rsp+0x78],r14
mov    QWORD PTR [rsp+0x80],0xc
lea    rdi,[rsp+0x398]
call   QWORD PTR [RIP:std::time::Instant::elapsed]
movq   xmm0,rax
punpckldq xmm0,XMMWORD PTR [RIP:GCC_except_table365+0xe4]
subpd  xmm0,XMMWORD PTR [RIP:GCC_except_table365+0x34]
movapd xmm1,xmm0
unpckhpd xmm1,xmm0
addsd  xmm1,xmm0
xorps  xmm0,xmm0
cvtsi2sd xmm0,edx
divsd  xmm0,QWORD PTR [RIP:GCC_except_table365+0x4dc]
addsd  xmm0,xmm1
mov    rdi,r12
call   QWORD PTR [RIP:serde_json::value::from::<impl core::convert::From<f64> for serde_json::value::Value>::from]
cmp    BYTE PTR [rsp+0x90],0x6
je     LOCAL+0x2bd7
movdqu xmm0,XMMWORD PTR [rsp+0x90]
movdqu xmm1,XMMWORD PTR [rsp+0xa0]
movdqa XMMWORD PTR [rsp+0x20],xmm1
movdqa XMMWORD PTR [rsp+0x10],xmm0
mov    rdi,r12
lea    rsi,[rsp+0x160]
lea    rdx,[rsp+0x70]
lea    rcx,[rsp+0x10]
call   alloc::collections::btree::map::BTreeMap<K,V,A>::insert
cmp    BYTE PTR [rsp+0x90],0x6
je     LOCAL+0x2728
mov    rdi,r12
call   core::ptr::drop_in_place<serde_json::value::Value>
mov    rax,QWORD PTR [rsp+0x170]
lea    rcx,[rsp+0x198]
mov    QWORD PTR [rcx+0x10],rax
movdqu xmm0,XMMWORD PTR [rsp+0x160]
movdqu XMMWORD PTR [rcx],xmm0
mov    BYTE PTR [rsp+0x190],0x5
lea    r14,[rsp+0x190]
mov    QWORD PTR [rsp+0x220],r14
mov    rax,QWORD PTR [RIP:<serde_json::value::Value as core::fmt::Display>::fmt]
mov    QWORD PTR [rsp+0x228],rax
lea    rdi,[RIP:anon.d5090c25a416dcf11afff7dd91233e4e.0.llvm.13100340739265517091+0x127]
lea    rsi,[rsp+0x220]
call   QWORD PTR [RIP:std::io::stdio::_print]
mov    rdi,r14
call   core::ptr::drop_in_place<serde_json::value::Value>
mov    r15,QWORD PTR [rsp+0x310]
lea    r14,[RIP:__frame_dummy_init_array_entry+0xf8]
mov    rax,QWORD PTR [rsp+0x110]
cmp    QWORD PTR [rax+0x8],0x5
jb     LOCAL+0x27e0
mov    rax,QWORD PTR [rax]
mov    ecx,DWORD PTR [rax]
mov    edx,0x6b73616d
xor    ecx,edx
movzx  eax,BYTE PTR [rax+0x4]
xor    eax,0x2d
or     eax,ecx
jne    LOCAL+0x27e0
mov    rax,QWORD PTR [rsp+0x370]
or     rax,QWORD PTR [rsp+0x360]
jne    LOCAL+0x2d1e
nop    DWORD PTR [rax+rax*1+0x0]
mov    rax,QWORD PTR [rsp+0x2e0]
or     rax,QWORD PTR [rsp+0x2e8]
jne    LOCAL+0x2c0e
movabs rax,0x8000000000000000
cmp    QWORD PTR [rsp+0x118],rax
je     LOCAL+0x2844
lea    rdi,[rsp+0x118]
call   <std::io::buffered::bufwriter::BufWriter<W> as core::ops::drop::Drop>::drop
mov    rsi,QWORD PTR [rsp+0x118]
test   rsi,rsi
je     LOCAL+0x2837
mov    rdi,QWORD PTR [rsp+0x120]
mov    edx,0x1
call   QWORD PTR [RIP:__rustc::__rust_dealloc]
mov    edi,DWORD PTR [rsp+0x134]
call   QWORD PTR [RIP:close@GLIBC_2.2.5]
mov    r13,QWORD PTR [rsp+0x1e0]
cmp    r13,0xc0
mov    rcx,QWORD PTR [RIP:std::time::Instant::now]
jne    LOCAL+0x515
lea    rdi,[rsp+0x388]
call   QWORD PTR [RIP:std::time::Instant::elapsed]
movq   xmm0,rax
punpckldq xmm0,XMMWORD PTR [RIP:GCC_except_table365+0xe4]
subpd  xmm0,XMMWORD PTR [RIP:GCC_except_table365+0x34]
movapd xmm1,xmm0
unpckhpd xmm1,xmm0
cvtsi2sd xmm2,edx
addsd  xmm1,xmm0
divsd  xmm2,QWORD PTR [RIP:GCC_except_table365+0x4dc]
addsd  xmm2,xmm1
movsd  QWORD PTR [rsp+0x90],xmm2
mov    QWORD PTR [rsp+0x220],r12
mov    rax,QWORD PTR [RIP:core::fmt::float::<impl core::fmt::Display for f64>::fmt]
mov    QWORD PTR [rsp+0x228],rax
lea    rdi,[RIP:anon.4227ec7036ba7d8315078e57be449868.0.llvm.13362339970539153419+0x1ab]
lea    rsi,[rsp+0x220]
call   QWORD PTR [RIP:std::io::stdio::_eprint]
mov    rbx,QWORD PTR [rsp+0x200]
mov    r14,QWORD PTR [rsp+0x208]
test   r14,r14
je     LOCAL+0x2932
lea    r15,[rbx+0x8]
jmp    LOCAL+0x2919
xor    r13d,r13d
mov    rdi,r13
mov    rsi,r15
call   QWORD PTR [RIP:alloc::raw_vec::handle_error]
jmp    LOCAL+0x2e59
data16 data16 data16 cs nop WORD PTR [rax+rax*1+0x0]
add    r15,0x18
dec    r14
je     LOCAL+0x2932
mov    rsi,QWORD PTR [r15-0x8]
test   rsi,rsi
je     LOCAL+0x2910
mov    rdi,QWORD PTR [r15]
mov    edx,0x1
call   QWORD PTR [RIP:__rustc::__rust_dealloc]
jmp    LOCAL+0x2910
mov    rax,QWORD PTR [rsp+0x1f8]
test   rax,rax
je     LOCAL+0x2955
shl    rax,0x3
lea    rsi,[rax+rax*2]
mov    edx,0x8
mov    rdi,rbx
call   QWORD PTR [RIP:__rustc::__rust_dealloc]
add    rsp,0x3c8
pop    rbx
pop    r12
pop    r13
pop    r14
pop    r15
pop    rbp
ret
mov    QWORD PTR [rsp+0x70],rax
lea    rdi,[RIP:GCC_except_table365+0x590]
lea    rcx,[RIP:__frame_dummy_init_array_entry+0x8]
lea    r8,[RIP:__frame_dummy_init_array_entry+0x260]
lea    rdx,[rsp+0x70]
mov    esi,0x2b
call   QWORD PTR [RIP:core::result::unwrap_failed]
jmp    LOCAL+0x2e59
mov    rax,QWORD PTR [rsp+0x228]
mov    ecx,DWORD PTR [rsp+0x230]
mov    QWORD PTR [rsp+0x90],rax
mov    DWORD PTR [rsp+0x98],ecx
lea    rdi,[RIP:GCC_except_table365+0x590]
lea    rcx,[RIP:__frame_dummy_init_array_entry+0x28]
lea    r8,[RIP:__frame_dummy_init_array_entry+0x2d8]
lea    rdx,[rsp+0x90]
mov    esi,0x2b
call   QWORD PTR [RIP:core::result::unwrap_failed]
jmp    LOCAL+0x2e59
lea    rdi,[RIP:anon.cc9e1b464619ab62d021e6446458583c.8.llvm.15800808401943094617+0x51c]
lea    rdx,[RIP:__frame_dummy_init_array_entry+0x230]
mov    esi,0x1d
call   QWORD PTR [RIP:core::panicking::panic_fmt]
jmp    LOCAL+0x2e59
add    dl,0xd0
xor    eax,eax
cmp    dl,0xa
adc    al,0x1
mov    BYTE PTR [rsp+0x220],al
lea    rdi,[RIP:GCC_except_table365+0x590]
lea    rcx,[RIP:__frame_dummy_init_array_entry+0x48]
lea    r8,[RIP:__frame_dummy_init_array_entry+0xc8]
lea    rdx,[rsp+0x220]
mov    esi,0x2b
call   QWORD PTR [RIP:core::result::unwrap_failed]
jmp    LOCAL+0x2e59
mov    rax,QWORD PTR [rsp+0x228]
mov    QWORD PTR [rsp+0x10],rax
lea    rdi,[RIP:GCC_except_table365+0x590]
lea    rcx,[RIP:__frame_dummy_init_array_entry+0x8]
lea    r8,[RIP:__frame_dummy_init_array_entry+0x1b8]
lea    rdx,[rsp+0x10]
mov    esi,0x2b
call   QWORD PTR [RIP:core::result::unwrap_failed]
jmp    LOCAL+0x2e59
mov    QWORD PTR [rsp+0x220],rax
lea    rdi,[RIP:GCC_except_table365+0x590]
lea    rcx,[RIP:__frame_dummy_init_array_entry+0x8]
lea    r8,[RIP:__frame_dummy_init_array_entry+0x1d0]
lea    rdx,[rsp+0x220]
mov    esi,0x2b
call   QWORD PTR [RIP:core::result::unwrap_failed]
jmp    LOCAL+0x2e59
mov    rax,QWORD PTR [rsp+0x98]
mov    QWORD PTR [rsp+0x10],rax
lea    rdi,[RIP:GCC_except_table365+0x590]
lea    rcx,[RIP:__frame_dummy_init_array_entry+0x68]
lea    r8,[RIP:__frame_dummy_init_array_entry+0x1e8]
lea    rdx,[rsp+0x10]
mov    esi,0x2b
call   QWORD PTR [RIP:core::result::unwrap_failed]
jmp    LOCAL+0x2e59
mov    rax,QWORD PTR [rsp+0x98]
mov    QWORD PTR [rsp+0x10],rax
lea    rdi,[RIP:GCC_except_table365+0x590]
lea    rcx,[RIP:__frame_dummy_init_array_entry+0x68]
lea    r8,[RIP:__frame_dummy_init_array_entry+0x1e8]
lea    rdx,[rsp+0x10]
mov    esi,0x2b
call   QWORD PTR [RIP:core::result::unwrap_failed]
jmp    LOCAL+0x2e59
mov    rax,QWORD PTR [rsp+0x98]
mov    QWORD PTR [rsp+0x10],rax
lea    rdi,[RIP:GCC_except_table365+0x590]
lea    rcx,[RIP:__frame_dummy_init_array_entry+0x68]
lea    r8,[RIP:__frame_dummy_init_array_entry+0x1e8]
lea    rdx,[rsp+0x10]
mov    esi,0x2b
call   QWORD PTR [RIP:core::result::unwrap_failed]
jmp    LOCAL+0x2e59
mov    edi,0x8
mov    esi,0x40
call   QWORD PTR [RIP:alloc::alloc::handle_alloc_error]
jmp    LOCAL+0x2e59
mov    rax,QWORD PTR [rsp+0x98]
mov    QWORD PTR [rsp+0x10],rax
lea    rdi,[RIP:GCC_except_table365+0x590]
lea    rcx,[RIP:__frame_dummy_init_array_entry+0x68]
lea    r8,[RIP:__frame_dummy_init_array_entry+0x1e8]
lea    rdx,[rsp+0x10]
mov    esi,0x2b
call   QWORD PTR [RIP:core::result::unwrap_failed]
jmp    LOCAL+0x2e59
mov    rax,QWORD PTR [rsp+0x98]
mov    QWORD PTR [rsp+0x218],rax
lea    rdi,[RIP:GCC_except_table365+0x590]
lea    rcx,[RIP:__frame_dummy_init_array_entry+0x68]
lea    r8,[RIP:__frame_dummy_init_array_entry+0x1e8]
lea    rdx,[rsp+0x218]
mov    esi,0x2b
call   QWORD PTR [RIP:core::result::unwrap_failed]
jmp    LOCAL+0x2e59
mov    rax,QWORD PTR [rsp+0x98]
mov    QWORD PTR [rsp+0x10],rax
lea    rdi,[RIP:GCC_except_table365+0x590]
lea    rcx,[RIP:__frame_dummy_init_array_entry+0x68]
lea    r8,[RIP:__frame_dummy_init_array_entry+0x1e8]
lea    rdx,[rsp+0x10]
mov    esi,0x2b
call   QWORD PTR [RIP:core::result::unwrap_failed]
jmp    LOCAL+0x2e59
mov    esi,0x55
lea    rdx,[RIP:__frame_dummy_init_array_entry+0x200]
lea    rdi,[RIP:anon.cc9e1b464619ab62d021e6446458583c.8.llvm.15800808401943094617+0x4d1]
jmp    LOCAL+0x2d31
mov    rax,QWORD PTR [rsp+0x228]
mov    QWORD PTR [rsp+0x90],rax
lea    rdi,[RIP:anon.cc9e1b464619ab62d021e6446458583c.8.llvm.15800808401943094617+0x57f]
lea    rcx,[RIP:__frame_dummy_init_array_entry+0x8]
lea    r8,[RIP:__frame_dummy_init_array_entry+0x2f0]
lea    rdx,[rsp+0x90]
mov    esi,0x1d
call   QWORD PTR [RIP:core::result::unwrap_failed]
jmp    LOCAL+0x2e59
mov    rax,QWORD PTR [rsp+0x228]
mov    QWORD PTR [rsp+0x90],rax
lea    rdi,[RIP:GCC_except_table365+0x590]
lea    rcx,[RIP:__frame_dummy_init_array_entry+0x68]
lea    r8,[RIP:__frame_dummy_init_array_entry+0x308]
lea    rdx,[rsp+0x90]
mov    esi,0x2b
call   QWORD PTR [RIP:core::result::unwrap_failed]
jmp    LOCAL+0x2e59
lea    rdi,[RIP:anon.cc9e1b464619ab62d021e6446458583c.8.llvm.15800808401943094617+0x5a1]
lea    rdx,[RIP:__frame_dummy_init_array_entry+0x338]
mov    esi,0xd
call   QWORD PTR [RIP:core::option::expect_failed]
jmp    LOCAL+0x2e59
mov    rax,QWORD PTR [rsp+0x228]
mov    ecx,DWORD PTR [rsp+0x230]
mov    QWORD PTR [rsp+0x10],rax
mov    DWORD PTR [rsp+0x18],ecx
lea    rdi,[RIP:GCC_except_table365+0x590]
lea    rcx,[RIP:__frame_dummy_init_array_entry+0x28]
lea    r8,[RIP:__frame_dummy_init_array_entry+0x2d8]
lea    rdx,[rsp+0x10]
mov    esi,0x2b
call   QWORD PTR [RIP:core::result::unwrap_failed]
jmp    LOCAL+0x2e59
lea    rdi,[RIP:anon.cc9e1b464619ab62d021e6446458583c.8.llvm.15800808401943094617+0x51c]
lea    rdx,[RIP:__frame_dummy_init_array_entry+0x320]
mov    esi,0x1d
call   QWORD PTR [RIP:core::panicking::panic_fmt]
jmp    LOCAL+0x2e59
mov    esi,0x43
lea    rdi,[RIP:anon.cc9e1b464619ab62d021e6446458583c.8.llvm.15800808401943094617+0x4fb]
lea    rdx,[RIP:__frame_dummy_init_array_entry+0x218]
call   QWORD PTR [RIP:core::panicking::panic_fmt]
jmp    LOCAL+0x2e59
lea    rax,[RIP:__frame_dummy_init_array_entry+0x290]
mov    rdi,rdx
mov    rsi,r15
mov    rdx,rax
call   QWORD PTR [RIP:core::panicking::panic_bounds_check]
jmp    LOCAL+0x2e59
mov    edi,0x4
mov    esi,0x40
call   QWORD PTR [RIP:alloc::raw_vec::handle_error]
jmp    LOCAL+0x2e59
lea    rax,[RIP:__frame_dummy_init_array_entry+0x278]
mov    rdi,rdx
mov    rsi,QWORD PTR [rsp+0xf8]
mov    rdx,rax
call   QWORD PTR [RIP:core::panicking::panic_bounds_check]
jmp    LOCAL+0x2e59
mov    al,0x1
jmp    LOCAL+0x2a09
lea    rdx,[RIP:__frame_dummy_init_array_entry+0x248]
mov    esi,0x2
call   QWORD PTR [RIP:core::panicking::panic_bounds_check]
jmp    LOCAL+0x2e59
mov    edi,0x4
mov    esi,0x10000
call   QWORD PTR [RIP:alloc::raw_vec::handle_error]
jmp    LOCAL+0x2e59
mov    edi,0x1
mov    rsi,r15
call   QWORD PTR [RIP:alloc::raw_vec::handle_error]
jmp    LOCAL+0x2e59
mov    edi,0x8
mov    rsi,QWORD PTR [rsp+0x138]
call   QWORD PTR [RIP:alloc::raw_vec::handle_error]
jmp    LOCAL+0x2e59
mov    edi,0x8
mov    rsi,QWORD PTR [rsp+0x1c8]
call   QWORD PTR [RIP:alloc::raw_vec::handle_error]
jmp    LOCAL+0x2e59
mov    edi,0x1
mov    esi,0x2000
call   QWORD PTR [RIP:alloc::raw_vec::handle_error]
jmp    LOCAL+0x2e59
mov    edi,0x1
mov    rsi,r15
call   QWORD PTR [RIP:alloc::raw_vec::handle_error]
jmp    LOCAL+0x2e59
lea    rdi,[RIP:anon.cc9e1b464619ab62d021e6446458583c.8.llvm.15800808401943094617+0x3ac]
lea    rdx,[RIP:__frame_dummy_init_array_entry+0xe0]
mov    esi,0x3e
call   QWORD PTR [RIP:core::panicking::panic]
jmp    LOCAL+0x2e59
xor    eax,eax
jmp    LOCAL+0x2a09
lea    rdx,[RIP:__frame_dummy_init_array_entry+0x2a8]
mov    esi,0x45
lea    rdi,[RIP:anon.cc9e1b464619ab62d021e6446458583c.8.llvm.15800808401943094617+0x52a]
call   QWORD PTR [RIP:core::panicking::panic_fmt]
ud2
mov    rbx,rax
mov    rsi,QWORD PTR [r12+0x8]
test   rsi,rsi
je     LOCAL+0x2e76
mov    rdx,QWORD PTR [r12+0x10]
mov    rdi,r15
call   QWORD PTR [RIP:__rustc::__rust_dealloc]
mov    esi,0x18
mov    edx,0x8
jmp    LOCAL+0x2f1e
mov    rbx,rax
jmp    LOCAL+0x3495
mov    rbx,rax
jmp    LOCAL+0x300f
mov    rbx,rax
lea    rdi,[rsp+0x190]
call   core::ptr::drop_in_place<serde_json::value::Value>
jmp    LOCAL+0x3474
jmp    LOCAL+0x2f72
jmp    LOCAL+0x2f72
mov    rbx,rax
jmp    LOCAL+0x307c
mov    rbx,rax
jmp    LOCAL+0x309b
jmp    LOCAL+0x2f72
mov    rbx,rax
jmp    LOCAL+0x30d8
jmp    LOCAL+0x2f72
mov    rbx,rax
jmp    LOCAL+0x30f5
jmp    LOCAL+0x2f72
jmp    LOCAL+0x2ee5
mov    rbx,rax
jmp    LOCAL+0x3112
jmp    LOCAL+0x2f72
jmp    LOCAL+0x2f72
jmp    LOCAL+0x2f72
mov    rbx,rax
mov    edi,ebp
jmp    LOCAL+0x34bc
jmp    LOCAL+0x2fc6
mov    rbx,rax
mov    rsi,QWORD PTR [rsp+0x348]
test   rsi,rsi
je     LOCAL+0x34c2
mov    edx,0x1
mov    rdi,r14
call   QWORD PTR [RIP:__rustc::__rust_dealloc]
jmp    LOCAL+0x34c2
mov    rbx,rax
jmp    LOCAL+0x305c
jmp    LOCAL+0x3155
mov    rbx,rax
mov    edx,0x8
mov    rdi,r14
mov    rsi,QWORD PTR [rsp+0x138]
call   QWORD PTR [RIP:__rustc::__rust_dealloc]
xor    ebp,ebp
mov    rax,QWORD PTR [rsp+0x178]
mov    QWORD PTR [rsp+0xf8],rax
jmp    LOCAL+0x2f8a
jmp    LOCAL+0x3155
jmp    LOCAL+0x33a1
jmp    LOCAL+0x2f72
mov    rbx,rax
jmp    LOCAL+0x33ef
mov    rbx,rax
jmp    LOCAL+0x31ae
jmp    LOCAL+0x2fe4
mov    rbx,rax
mov    bpl,0x1
cmp    QWORD PTR [rsp+0xf8],0x0
je     LOCAL+0x2fb4
mov    rdi,QWORD PTR [rsp+0x180]
mov    rsi,QWORD PTR [rsp+0xf8]
shl    rsi,0x3
mov    edx,0x8
call   QWORD PTR [RIP:__rustc::__rust_dealloc]
test   bpl,bpl
jne    LOCAL+0x2fc9
jmp    LOCAL+0x3474
mov    rbx,rax
jmp    LOCAL+0x31c1
mov    rbx,rax
mov    edx,0x8
mov    rdi,r14
mov    rsi,QWORD PTR [rsp+0x138]
call   QWORD PTR [RIP:__rustc::__rust_dealloc]
jmp    LOCAL+0x3474
mov    rbx,rax
cmp    BYTE PTR [rsp+0x104],0x0
je     LOCAL+0x3198
jmp    LOCAL+0x31ae
jmp    LOCAL+0x33a9
mov    rbx,rax
lea    rdi,[rsp+0x90]
call   core::ptr::drop_in_place<serde_json::error::Error>
test   r14,r14
je     LOCAL+0x34c2
mov    edx,0x1
mov    rdi,r15
mov    rsi,r14
call   QWORD PTR [RIP:__rustc::__rust_dealloc]
jmp    LOCAL+0x34c2
call   QWORD PTR [RIP:core::panicking::panic_in_cleanup]
mov    rbx,rax
lea    rdi,[rsp+0x90]
call   core::ptr::drop_in_place<std::io::error::Error>
jmp    LOCAL+0x34c2
call   QWORD PTR [RIP:core::panicking::panic_in_cleanup]
mov    rbx,rax
lea    rdi,[rsp+0x10]
call   core::ptr::drop_in_place<serde_json::error::Error>
mov    esi,0xc
jmp    LOCAL+0x33e1
call   QWORD PTR [RIP:core::panicking::panic_in_cleanup]
mov    rbx,rax
lea    rdi,[rsp+0x218]
call   core::ptr::drop_in_place<serde_json::error::Error>
lea    rdi,[rsp+0x10]
call   core::ptr::drop_in_place<serde_json::value::Value>
jmp    LOCAL+0x309b
call   QWORD PTR [RIP:core::panicking::panic_in_cleanup]
mov    rbx,rax
lea    rdi,[rsp+0x10]
call   core::ptr::drop_in_place<serde_json::error::Error>
mov    esi,0x40
mov    edx,0x8
mov    rdi,r15
call   QWORD PTR [RIP:__rustc::__rust_dealloc]
mov    esi,0xb
jmp    LOCAL+0x33e1
call   QWORD PTR [RIP:core::panicking::panic_in_cleanup]
mov    rbx,rax
mov    esi,0xb
jmp    LOCAL+0x33e1
mov    rbx,rax
lea    rdi,[rsp+0x10]
call   core::ptr::drop_in_place<serde_json::error::Error>
mov    esi,0x13
jmp    LOCAL+0x33e1
call   QWORD PTR [RIP:core::panicking::panic_in_cleanup]
mov    rbx,rax
lea    rdi,[rsp+0x10]
call   core::ptr::drop_in_place<serde_json::error::Error>
mov    esi,0xa
jmp    LOCAL+0x33e1
call   QWORD PTR [RIP:core::panicking::panic_in_cleanup]
mov    rbx,rax
lea    rdi,[rsp+0x10]
call   core::ptr::drop_in_place<serde_json::error::Error>
mov    esi,0x5
jmp    LOCAL+0x33e1
call   QWORD PTR [RIP:core::panicking::panic_in_cleanup]
mov    rbx,rax
lea    rdi,[rsp+0x220]
call   core::ptr::drop_in_place<std::io::error::Error>
jmp    LOCAL+0x3474
call   QWORD PTR [RIP:core::panicking::panic_in_cleanup]
mov    rbx,rax
lea    rdi,[rsp+0x10]
call   core::ptr::drop_in_place<std::io::error::Error>
jmp    LOCAL+0x34c2
call   QWORD PTR [RIP:core::panicking::panic_in_cleanup]
mov    rbx,rax
jmp    LOCAL+0x3474
mov    rbx,rax
lea    rdi,[rsp+0x90]
call   core::ptr::drop_in_place<serde_json::value::Value>
jmp    LOCAL+0x34c2
call   QWORD PTR [RIP:core::panicking::panic_in_cleanup]
mov    rbx,rax
mov    rax,QWORD PTR [rsp+0x70]
mov    ecx,eax
and    ecx,0x3
cmp    ecx,0x1
je     LOCAL+0x3318
cmp    BYTE PTR [rsp+0x104],0x0
jne    LOCAL+0x31ae
mov    edx,0x4
mov    rdi,r14
mov    rsi,QWORD PTR [rsp+0x1e8]
call   QWORD PTR [RIP:__rustc::__rust_dealloc]
mov    esi,0x40
mov    edx,0x4
mov    rdi,rbp
call   QWORD PTR [RIP:__rustc::__rust_dealloc]
mov    BYTE PTR [rsp+0x18],0x0
mov    BYTE PTR [rsp+0x19],0x0
mov    BYTE PTR [rsp+0x1a],0x0
mov    BYTE PTR [rsp+0x1b],0x0
mov    BYTE PTR [rsp+0x1c],0x0
mov    BYTE PTR [rsp+0x1d],0x0
mov    BYTE PTR [rsp+0x1e],0x0
mov    BYTE PTR [rsp+0x1f],0x0
mov    BYTE PTR [rsp+0x20],0x0
mov    BYTE PTR [rsp+0x21],0x0
mov    BYTE PTR [rsp+0x22],0x0
mov    BYTE PTR [rsp+0x23],0x0
mov    BYTE PTR [rsp+0x24],0x0
mov    BYTE PTR [rsp+0x25],0x0
mov    BYTE PTR [rsp+0x26],0x0
mov    BYTE PTR [rsp+0x27],0x0
mov    BYTE PTR [rsp+0x28],0x0
mov    BYTE PTR [rsp+0x29],0x0
mov    BYTE PTR [rsp+0x2a],0x0
mov    BYTE PTR [rsp+0x2b],0x0
mov    BYTE PTR [rsp+0x2c],0x0
mov    BYTE PTR [rsp+0x2d],0x0
mov    BYTE PTR [rsp+0x2e],0x0
mov    BYTE PTR [rsp+0x2f],0x0
mov    BYTE PTR [rsp+0x30],0x0
mov    BYTE PTR [rsp+0x31],0x0
mov    BYTE PTR [rsp+0x32],0x0
mov    BYTE PTR [rsp+0x33],0x0
mov    BYTE PTR [rsp+0x34],0x0
mov    BYTE PTR [rsp+0x35],0x0
mov    BYTE PTR [rsp+0x36],0x0
mov    BYTE PTR [rsp+0x37],0x0
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
mov    BYTE PTR [rsp+0x50],0x0
mov    BYTE PTR [rsp+0x51],0x0
mov    BYTE PTR [rsp+0x52],0x0
mov    BYTE PTR [rsp+0x53],0x0
mov    BYTE PTR [rsp+0x54],0x0
mov    BYTE PTR [rsp+0x55],0x0
mov    BYTE PTR [rsp+0x56],0x0
mov    BYTE PTR [rsp+0x57],0x0
mov    BYTE PTR [rsp+0x58],0x0
mov    BYTE PTR [rsp+0x59],0x0
mov    BYTE PTR [rsp+0x5a],0x0
mov    BYTE PTR [rsp+0x5b],0x0
mov    BYTE PTR [rsp+0x5c],0x0
mov    BYTE PTR [rsp+0x5d],0x0
mov    BYTE PTR [rsp+0x5e],0x0
mov    BYTE PTR [rsp+0x5f],0x0
mov    QWORD PTR [rsp+0x38],0x0
mov    QWORD PTR [rsp+0x60],0x0
jmp    LOCAL+0x33ac
lea    r15,[rax-0x1]
mov    r13,QWORD PTR [rax-0x1]
mov    r12,QWORD PTR [rax+0x7]
mov    rax,QWORD PTR [r12]
test   rax,rax
je     LOCAL+0x3332
mov    rdi,r13
call   rax
mov    rsi,QWORD PTR [r12+0x8]
test   rsi,rsi
je     LOCAL+0x334a
mov    rdx,QWORD PTR [r12+0x10]
mov    rdi,r13
call   QWORD PTR [RIP:__rustc::__rust_dealloc]
mov    esi,0x18
mov    edx,0x8
mov    rdi,r15
call   QWORD PTR [RIP:__rustc::__rust_dealloc]
cmp    BYTE PTR [rsp+0x104],0x0
je     LOCAL+0x3198
jmp    LOCAL+0x31ae
mov    rsi,QWORD PTR [r12+0x8]
test   rsi,rsi
je     LOCAL+0x3388
mov    rdx,QWORD PTR [r12+0x10]
mov    rdi,r13
call   QWORD PTR [RIP:__rustc::__rust_dealloc]
mov    esi,0x18
mov    edx,0x8
mov    rdi,r15
call   QWORD PTR [RIP:__rustc::__rust_dealloc]
call   QWORD PTR [RIP:core::panicking::panic_in_cleanup]
mov    rbx,rax
jmp    LOCAL+0x34c2
mov    rbx,rax
mov    rsi,QWORD PTR [rsp+0x1d8]
test   rsi,rsi
je     LOCAL+0x3474
shl    rsi,0x3
mov    edx,0x8
mov    rdi,QWORD PTR [rsp+0x1d0]
call   QWORD PTR [RIP:__rustc::__rust_dealloc]
jmp    LOCAL+0x3474
mov    rbx,rax
mov    esi,0x6
mov    edx,0x1
mov    rdi,r14
call   QWORD PTR [RIP:__rustc::__rust_dealloc]
mov    rcx,QWORD PTR [rsp+0x160]
test   rcx,rcx
jne    LOCAL+0x3402
xor    ecx,ecx
xor    eax,eax
jmp    LOCAL+0x344f
mov    rdx,QWORD PTR [rsp+0x168]
mov    rax,QWORD PTR [rsp+0x170]
mov    QWORD PTR [rsp+0x228],0x0
mov    QWORD PTR [rsp+0x230],rcx
mov    QWORD PTR [rsp+0x238],rdx
mov    QWORD PTR [rsp+0x248],0x0
mov    QWORD PTR [rsp+0x250],rcx
mov    QWORD PTR [rsp+0x258],rdx
mov    ecx,0x1
mov    QWORD PTR [rsp+0x220],rcx
mov    QWORD PTR [rsp+0x240],rcx
mov    QWORD PTR [rsp+0x260],rax
lea    rdi,[rsp+0x220]
call   core::ptr::drop_in_place<alloc::collections::btree::map::IntoIter<alloc::string::String,serde_json::value::Value>>
movabs rax,0x8000000000000000
cmp    QWORD PTR [rsp+0x118],rax
je     LOCAL+0x34c2
lea    rdi,[rsp+0x118]
call   <std::io::buffered::bufwriter::BufWriter<W> as core::ops::drop::Drop>::drop
mov    rsi,QWORD PTR [rsp+0x118]
test   rsi,rsi
je     LOCAL+0x34b5
mov    rdi,QWORD PTR [rsp+0x120]
mov    edx,0x1
call   QWORD PTR [RIP:__rustc::__rust_dealloc]
mov    edi,DWORD PTR [rsp+0x134]
call   QWORD PTR [RIP:close@GLIBC_2.2.5]
mov    r14,QWORD PTR [rsp+0x200]
mov    r15,QWORD PTR [rsp+0x208]
test   r15,r15
jne    LOCAL+0x3502
mov    rax,QWORD PTR [rsp+0x1f8]
test   rax,rax
je     LOCAL+0x34fa
shl    rax,0x3
lea    rsi,[rax+rax*2]
mov    edx,0x8
mov    rdi,r14
call   QWORD PTR [RIP:__rustc::__rust_dealloc]
mov    rdi,rbx
call   _Unwind_Resume@plt
lea    r12,[r14+0x8]
mov    r13,QWORD PTR [RIP:__rustc::__rust_dealloc]
jmp    LOCAL+0x3519
nop
add    r12,0x18
dec    r15
je     LOCAL+0x34d7
mov    rsi,QWORD PTR [r12-0x8]
test   rsi,rsi
je     LOCAL+0x3510
mov    rdi,QWORD PTR [r12]
mov    edx,0x1
call   r13
jmp    LOCAL+0x3510
mov    rsi,QWORD PTR [rsp+0x118]
test   rsi,rsi
je     LOCAL+0x3551
mov    rdi,QWORD PTR [rsp+0x120]
mov    edx,0x1
call   QWORD PTR [RIP:__rustc::__rust_dealloc]
mov    edi,DWORD PTR [rsp+0x134]
call   QWORD PTR [RIP:close@GLIBC_2.2.5]
call   QWORD PTR [RIP:core::panicking::panic_in_cleanup]
call   QWORD PTR [RIP:core::panicking::panic_in_cleanup]
int3
int3
int3
int3
int3
int3

pv_dudect::inverse_m @ 0x33460
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

pv_dudect::kernels::state_only_hiding::measure_qm31 @ 0x37850
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
lea    rax,[RIP:anon.cc9e1b464619ab62d021e6446458583c.0.llvm.15800808401943094617+0x1c]
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
lea    rax,[RIP:anon.cc9e1b464619ab62d021e6446458583c.0.llvm.15800808401943094617+0x1c]
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
lea    rax,[RIP:anon.cc9e1b464619ab62d021e6446458583c.0.llvm.15800808401943094617+0x1c]
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
lea    rax,[RIP:anon.cc9e1b464619ab62d021e6446458583c.0.llvm.15800808401943094617+0x1c]
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
lea    rcx,[RIP:anon.cc9e1b464619ab62d021e6446458583c.4.llvm.15800808401943094617+0x30]
mov    edx,0x20
call   QWORD PTR [RIP:core::slice::index::slice_index_fail]
int3
int3
int3
int3
int3
int3

pv_dudect::kernels::entropy::seed_check @ 0x38070
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
