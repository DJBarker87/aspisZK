aspis_r1_cost_probe::host_semantic::copy_tuple_limb @ 0xb91a0
xor    eax,eax
cmp    BYTE PTR [rdx],0x1
jne    LOCAL+0x6a
movzx  ecx,WORD PTR [rdx+0x2]
movzx  r8d,BYTE PTR [rdx+0x4]
mov    eax,DWORD PTR [rdx+0x8]
cmp    BYTE PTR [rdx+0x6],0x0
je     LOCAL+0x38
mov    dl,0xa
cmp    r8b,0xf
ja     LOCAL+0x6f
lea    r9,[r8+r8*2]
cmp    QWORD PTR [rsi+r9*8+0x190],rcx
jbe    LOCAL+0x6f
add    rsi,0x180
jmp    LOCAL+0x4b
mov    dl,0xa
cmp    r8b,0xf
ja     LOCAL+0x6f
lea    r9,[r8+r8*2]
cmp    QWORD PTR [rsi+r9*8+0x10],rcx
jbe    LOCAL+0x6f
lea    rdx,[r8+r8*2]
mov    rdx,QWORD PTR [rsi+rdx*8+0x8]
mov    ecx,DWORD PTR [rdx+rcx*4]
lea    edx,[rcx+rax*1]
cmp    edx,0x7fffffff
lea    eax,[rcx+rax*1-0x7fffffff]
cmovb  eax,edx
mov    DWORD PTR [rdi+0x4],eax
mov    dl,0xc
mov    BYTE PTR [rdi],dl
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
