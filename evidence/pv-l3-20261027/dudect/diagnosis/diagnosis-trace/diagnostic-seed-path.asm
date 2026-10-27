0000000000025bf0 <diagnostic::kernels::state_only_hiding::measure_m31>:
   25bf0:	push   rbp
   25bf1:	push   r15
   25bf3:	push   r14
   25bf5:	push   r13
   25bf7:	push   r12
   25bf9:	push   rbx
   25bfa:	sub    rsp,0x88
   25c01:	mov    rbx,rdi
   25c04:	mov    rcx,QWORD PTR [rdi+0x50]
   25c08:	mov    r12,QWORD PTR [rdi]
   25c0b:	mov    r13,QWORD PTR [rdi+0x28]
   25c0f:	lea    rbp,[rdi+0x8]
   25c13:	lea    r14,[rdi+0x30]
   25c17:	mov    r15d,0x10
   25c1d:	nop    DWORD PTR [rax]
   25c20:	cmp    rcx,0x8
   25c24:	je     25c60 <diagnostic::kernels::state_only_hiding::measure_m31+0x70>
   25c26:	lea    rdi,[rcx*4+0x0]
   25c2e:	inc    rcx
   25c31:	mov    QWORD PTR [rbx+0x50],rcx
   25c35:	cmp    rdi,0x20
   25c39:	jae    25d2a <diagnostic::kernels::state_only_hiding::measure_m31+0x13a>
   25c3f:	mov    eax,DWORD PTR [r14+rdi*1]
   25c43:	and    eax,0x7fffffff
   25c48:	cmp    rax,0x7fffffff
   25c4e:	je     25cfe <diagnostic::kernels::state_only_hiding::measure_m31+0x10e>
   25c54:	jmp    25d0e <diagnostic::kernels::state_only_hiding::measure_m31+0x11e>
   25c59:	nop    DWORD PTR [rax+0x0]
   25c60:	movups xmm0,XMMWORD PTR [rbp+0x0]
   25c64:	movups xmm1,XMMWORD PTR [rbp+0x10]
   25c68:	movaps XMMWORD PTR [rsp+0x50],xmm1
   25c6d:	movaps XMMWORD PTR [rsp+0x40],xmm0
   25c72:	mov    QWORD PTR [rsp+0x8],r13
   25c77:	lea    rax,[rip+0xffffffffffff2914]        # 18592 <anon.3bf34360074acd75cadd6d98e3825a38.6.llvm.5796641766152556861+0xd7b>
   25c7e:	mov    QWORD PTR [rsp+0x10],rax
   25c83:	mov    QWORD PTR [rsp+0x18],0x27
   25c8c:	lea    rax,[rsp+0x40]
   25c91:	mov    QWORD PTR [rsp+0x20],rax
   25c96:	mov    QWORD PTR [rsp+0x28],0x20
   25c9f:	lea    rax,[rsp+0x8]
   25ca4:	mov    QWORD PTR [rsp+0x30],rax
   25ca9:	mov    QWORD PTR [rsp+0x38],0x8
   25cb2:	mov    edx,0x3
   25cb7:	lea    rdi,[rsp+0x68]
   25cbc:	lea    rsi,[rsp+0x10]
   25cc1:	call   r12
   25cc4:	movups xmm0,XMMWORD PTR [rsp+0x68]
   25cc9:	movups xmm1,XMMWORD PTR [rsp+0x78]
   25cce:	movups XMMWORD PTR [r14+0x10],xmm1
   25cd3:	movups XMMWORD PTR [r14],xmm0
   25cd7:	inc    r13
   25cda:	mov    QWORD PTR [rbx+0x28],r13
   25cde:	mov    QWORD PTR [rbx+0x50],0x1
   25ce6:	mov    ecx,0x1
   25ceb:	xor    edi,edi
   25ced:	mov    eax,DWORD PTR [r14+rdi*1]
   25cf1:	and    eax,0x7fffffff
   25cf6:	cmp    rax,0x7fffffff
   25cfc:	jne    25d0e <diagnostic::kernels::state_only_hiding::measure_m31+0x11e>
   25cfe:	dec    r15
   25d01:	jne    25c20 <diagnostic::kernels::state_only_hiding::measure_m31+0x30>
   25d07:	mov    eax,0x201
   25d0c:	jmp    25d18 <diagnostic::kernels::state_only_hiding::measure_m31+0x128>
   25d0e:	shl    rax,0x20
   25d12:	or     rax,0x200
   25d18:	add    rsp,0x88
   25d1f:	pop    rbx
   25d20:	pop    r12
   25d22:	pop    r13
   25d24:	pop    r14
   25d26:	pop    r15
   25d28:	pop    rbp
   25d29:	ret
   25d2a:	lea    rsi,[rdi+0x4]
   25d2e:	lea    rcx,[rip+0x44f3b]        # 6ac70 <__frame_dummy_init_array_entry+0xe0>
   25d35:	mov    edx,0x20
   25d3a:	call   QWORD PTR [rip+0x47060]        # 6cda0 <_DYNAMIC+0x2b8>

0000000000025d40 <diagnostic::kernels::state_only_hiding::measure_qm31>:
   25d40:	push   rbp
   25d41:	push   r15
   25d43:	push   r14
   25d45:	push   r13
   25d47:	push   r12
   25d49:	push   rbx
   25d4a:	sub    rsp,0x98
   25d51:	mov    r14,rsi
   25d54:	mov    QWORD PTR [rsp+0x8],rdi
   25d59:	mov    rax,QWORD PTR [rsi+0x50]
   25d5d:	mov    rcx,QWORD PTR [rsi]
   25d60:	mov    QWORD PTR [rsp+0x18],rcx
   25d65:	mov    rdx,QWORD PTR [rsi+0x28]
   25d69:	lea    rcx,[rsi+0x8]
   25d6d:	mov    QWORD PTR [rsp+0x10],rcx
   25d72:	lea    r15,[rsi+0x30]
   25d76:	mov    ebx,0x10
   25d7b:	lea    r12,[rsp+0x20]
   25d80:	mov    ebp,0x7fffffff
   25d85:	data16 cs nop WORD PTR [rax+rax*1+0x0]
   25d90:	cmp    rax,0x8
   25d94:	je     25dd0 <diagnostic::kernels::state_only_hiding::measure_qm31+0x90>
   25d96:	lea    rdi,[rax*4+0x0]
   25d9e:	inc    rax
   25da1:	mov    QWORD PTR [r14+0x50],rax
   25da5:	cmp    rdi,0x20
   25da9:	jae    261d4 <diagnostic::kernels::state_only_hiding::measure_qm31+0x494>
   25daf:	mov    r13d,DWORD PTR [r15+rdi*1]
   25db3:	and    r13d,ebp
   25db6:	cmp    r13d,0x7fffffff
   25dbd:	je     25e76 <diagnostic::kernels::state_only_hiding::measure_qm31+0x136>
   25dc3:	jmp    25e84 <diagnostic::kernels::state_only_hiding::measure_qm31+0x144>
   25dc8:	nop    DWORD PTR [rax+rax*1+0x0]
   25dd0:	mov    rax,QWORD PTR [rsp+0x10]
   25dd5:	movups xmm0,XMMWORD PTR [rax]
   25dd8:	movups xmm1,XMMWORD PTR [rax+0x10]
   25ddc:	movaps XMMWORD PTR [rsp+0x60],xmm1
   25de1:	movaps XMMWORD PTR [rsp+0x50],xmm0
   25de6:	mov    QWORD PTR [rsp],rdx
   25dea:	lea    rax,[rip+0xffffffffffff27a1]        # 18592 <anon.3bf34360074acd75cadd6d98e3825a38.6.llvm.5796641766152556861+0xd7b>
   25df1:	mov    QWORD PTR [rsp+0x20],rax
   25df6:	mov    QWORD PTR [rsp+0x28],0x27
   25dff:	lea    rax,[rsp+0x50]
   25e04:	mov    QWORD PTR [rsp+0x30],rax
   25e09:	mov    QWORD PTR [rsp+0x38],0x20
   25e12:	mov    rax,rsp
   25e15:	mov    QWORD PTR [rsp+0x40],rax
   25e1a:	mov    QWORD PTR [rsp+0x48],0x8
   25e23:	mov    r13,rdx
   25e26:	mov    edx,0x3
   25e2b:	lea    rdi,[rsp+0x70]
   25e30:	mov    rsi,r12
   25e33:	call   QWORD PTR [rsp+0x18]
   25e37:	mov    rdx,r13
   25e3a:	movups xmm0,XMMWORD PTR [rsp+0x70]
   25e3f:	movups xmm1,XMMWORD PTR [rsp+0x80]
   25e47:	movups XMMWORD PTR [r15+0x10],xmm1
   25e4c:	movups XMMWORD PTR [r15],xmm0
   25e50:	inc    rdx
   25e53:	mov    QWORD PTR [r14+0x28],rdx
   25e57:	mov    QWORD PTR [r14+0x50],0x1
   25e5f:	mov    eax,0x1
   25e64:	xor    edi,edi
   25e66:	mov    r13d,DWORD PTR [r15+rdi*1]
   25e6a:	and    r13d,ebp
   25e6d:	cmp    r13d,0x7fffffff
   25e74:	jne    25e84 <diagnostic::kernels::state_only_hiding::measure_qm31+0x144>
   25e76:	dec    rbx
   25e79:	jne    25d90 <diagnostic::kernels::state_only_hiding::measure_qm31+0x50>
   25e7f:	jmp    2619e <diagnostic::kernels::state_only_hiding::measure_qm31+0x45e>
   25e84:	mov    ebx,0x10
   25e89:	mov    ebp,0x7fffffff
   25e8e:	xchg   ax,ax
   25e90:	cmp    rax,0x8
   25e94:	je     25ed0 <diagnostic::kernels::state_only_hiding::measure_qm31+0x190>
   25e96:	lea    rdi,[rax*4+0x0]
   25e9e:	inc    rax
   25ea1:	mov    QWORD PTR [r14+0x50],rax
   25ea5:	cmp    rdi,0x20
   25ea9:	jae    261d4 <diagnostic::kernels::state_only_hiding::measure_qm31+0x494>
   25eaf:	mov    r12d,DWORD PTR [r15+rdi*1]
   25eb3:	and    r12d,ebp
   25eb6:	cmp    r12d,0x7fffffff
   25ebd:	je     25f78 <diagnostic::kernels::state_only_hiding::measure_qm31+0x238>
   25ec3:	jmp    25f86 <diagnostic::kernels::state_only_hiding::measure_qm31+0x246>
   25ec8:	nop    DWORD PTR [rax+rax*1+0x0]
   25ed0:	mov    rax,QWORD PTR [rsp+0x10]
   25ed5:	movups xmm0,XMMWORD PTR [rax]
   25ed8:	movups xmm1,XMMWORD PTR [rax+0x10]
   25edc:	movaps XMMWORD PTR [rsp+0x60],xmm1
   25ee1:	movaps XMMWORD PTR [rsp+0x50],xmm0
   25ee6:	mov    QWORD PTR [rsp],rdx
   25eea:	lea    rax,[rip+0xffffffffffff26a1]        # 18592 <anon.3bf34360074acd75cadd6d98e3825a38.6.llvm.5796641766152556861+0xd7b>
   25ef1:	mov    QWORD PTR [rsp+0x20],rax
   25ef6:	mov    QWORD PTR [rsp+0x28],0x27
   25eff:	lea    rax,[rsp+0x50]
   25f04:	mov    QWORD PTR [rsp+0x30],rax
   25f09:	mov    QWORD PTR [rsp+0x38],0x20
   25f12:	mov    rax,rsp
   25f15:	mov    QWORD PTR [rsp+0x40],rax
   25f1a:	mov    QWORD PTR [rsp+0x48],0x8
   25f23:	mov    r12,rdx
   25f26:	mov    edx,0x3
   25f2b:	lea    rdi,[rsp+0x70]
   25f30:	lea    rsi,[rsp+0x20]
   25f35:	call   QWORD PTR [rsp+0x18]
   25f39:	mov    rdx,r12
   25f3c:	movups xmm0,XMMWORD PTR [rsp+0x70]
   25f41:	movups xmm1,XMMWORD PTR [rsp+0x80]
   25f49:	movups XMMWORD PTR [r15+0x10],xmm1
   25f4e:	movups XMMWORD PTR [r15],xmm0
   25f52:	inc    rdx
   25f55:	mov    QWORD PTR [r14+0x28],rdx
   25f59:	mov    QWORD PTR [r14+0x50],0x1
   25f61:	mov    eax,0x1
   25f66:	xor    edi,edi
   25f68:	mov    r12d,DWORD PTR [r15+rdi*1]
   25f6c:	and    r12d,ebp
   25f6f:	cmp    r12d,0x7fffffff
   25f76:	jne    25f86 <diagnostic::kernels::state_only_hiding::measure_qm31+0x246>
   25f78:	dec    rbx
   25f7b:	jne    25e90 <diagnostic::kernels::state_only_hiding::measure_qm31+0x150>
   25f81:	jmp    2619e <diagnostic::kernels::state_only_hiding::measure_qm31+0x45e>
   25f86:	mov    ebp,0x10
   25f8b:	mov    ecx,0x7fffffff
   25f90:	cmp    rax,0x8
   25f94:	je     25fd0 <diagnostic::kernels::state_only_hiding::measure_qm31+0x290>
   25f96:	lea    rdi,[rax*4+0x0]
   25f9e:	inc    rax
   25fa1:	mov    QWORD PTR [r14+0x50],rax
   25fa5:	cmp    rdi,0x20
   25fa9:	jae    261d4 <diagnostic::kernels::state_only_hiding::measure_qm31+0x494>
   25faf:	mov    ebx,DWORD PTR [r15+rdi*1]
   25fb3:	and    ebx,ecx
   25fb5:	cmp    ebx,0x7fffffff
   25fbb:	je     2607b <diagnostic::kernels::state_only_hiding::measure_qm31+0x33b>
   25fc1:	jmp    26089 <diagnostic::kernels::state_only_hiding::measure_qm31+0x349>
   25fc6:	cs nop WORD PTR [rax+rax*1+0x0]
   25fd0:	mov    rax,QWORD PTR [rsp+0x10]
   25fd5:	movups xmm0,XMMWORD PTR [rax]
   25fd8:	movups xmm1,XMMWORD PTR [rax+0x10]
   25fdc:	movaps XMMWORD PTR [rsp+0x60],xmm1
   25fe1:	movaps XMMWORD PTR [rsp+0x50],xmm0
   25fe6:	mov    QWORD PTR [rsp],rdx
   25fea:	lea    rax,[rip+0xffffffffffff25a1]        # 18592 <anon.3bf34360074acd75cadd6d98e3825a38.6.llvm.5796641766152556861+0xd7b>
   25ff1:	mov    QWORD PTR [rsp+0x20],rax
   25ff6:	mov    QWORD PTR [rsp+0x28],0x27
   25fff:	lea    rax,[rsp+0x50]
   26004:	mov    QWORD PTR [rsp+0x30],rax
   26009:	mov    QWORD PTR [rsp+0x38],0x20
   26012:	mov    rax,rsp
   26015:	mov    QWORD PTR [rsp+0x40],rax
   2601a:	mov    QWORD PTR [rsp+0x48],0x8
   26023:	mov    rbx,rdx
   26026:	mov    edx,0x3
   2602b:	lea    rdi,[rsp+0x70]
   26030:	lea    rsi,[rsp+0x20]
   26035:	call   QWORD PTR [rsp+0x18]
   26039:	mov    ecx,0x7fffffff
   2603e:	mov    rdx,rbx
   26041:	movups xmm0,XMMWORD PTR [rsp+0x70]
   26046:	movups xmm1,XMMWORD PTR [rsp+0x80]
   2604e:	movups XMMWORD PTR [r15+0x10],xmm1
   26053:	movups XMMWORD PTR [r15],xmm0
   26057:	inc    rdx
   2605a:	mov    QWORD PTR [r14+0x28],rdx
   2605e:	mov    QWORD PTR [r14+0x50],0x1
   26066:	mov    eax,0x1
   2606b:	xor    edi,edi
   2606d:	mov    ebx,DWORD PTR [r15+rdi*1]
   26071:	and    ebx,ecx
   26073:	cmp    ebx,0x7fffffff
   26079:	jne    26089 <diagnostic::kernels::state_only_hiding::measure_qm31+0x349>
   2607b:	dec    rbp
   2607e:	jne    25f90 <diagnostic::kernels::state_only_hiding::measure_qm31+0x250>
   26084:	jmp    2619e <diagnostic::kernels::state_only_hiding::measure_qm31+0x45e>
   26089:	mov    ebp,0x10
   2608e:	mov    esi,0x7fffffff
   26093:	data16 data16 data16 cs nop WORD PTR [rax+rax*1+0x0]
   260a0:	cmp    rax,0x8
   260a4:	je     260e0 <diagnostic::kernels::state_only_hiding::measure_qm31+0x3a0>
   260a6:	lea    rdi,[rax*4+0x0]
   260ae:	inc    rax
   260b1:	mov    QWORD PTR [r14+0x50],rax
   260b5:	cmp    rdi,0x20
   260b9:	jae    261d4 <diagnostic::kernels::state_only_hiding::measure_qm31+0x494>
   260bf:	mov    ecx,DWORD PTR [r15+rdi*1]
   260c3:	and    ecx,esi
   260c5:	cmp    ecx,0x7fffffff
   260cb:	je     26195 <diagnostic::kernels::state_only_hiding::measure_qm31+0x455>
   260d1:	jmp    261bd <diagnostic::kernels::state_only_hiding::measure_qm31+0x47d>
   260d6:	cs nop WORD PTR [rax+rax*1+0x0]
   260e0:	mov    rax,QWORD PTR [rsp+0x10]
   260e5:	movups xmm0,XMMWORD PTR [rax]
   260e8:	movups xmm1,XMMWORD PTR [rax+0x10]
   260ec:	movaps XMMWORD PTR [rsp+0x60],xmm1
   260f1:	movaps XMMWORD PTR [rsp+0x50],xmm0
   260f6:	mov    QWORD PTR [rsp],rdx
   260fa:	lea    rax,[rip+0xffffffffffff2491]        # 18592 <anon.3bf34360074acd75cadd6d98e3825a38.6.llvm.5796641766152556861+0xd7b>
   26101:	mov    QWORD PTR [rsp+0x20],rax
   26106:	mov    QWORD PTR [rsp+0x28],0x27
   2610f:	lea    rax,[rsp+0x50]
   26114:	mov    QWORD PTR [rsp+0x30],rax
   26119:	mov    QWORD PTR [rsp+0x38],0x20
   26122:	mov    rax,rsp
   26125:	mov    QWORD PTR [rsp+0x40],rax
   2612a:	mov    QWORD PTR [rsp+0x48],0x8
   26133:	mov    QWORD PTR [rsp+0x90],rdx
   2613b:	mov    edx,0x3
   26140:	lea    rdi,[rsp+0x70]
   26145:	lea    rsi,[rsp+0x20]
   2614a:	call   QWORD PTR [rsp+0x18]
   2614e:	mov    esi,0x7fffffff
   26153:	mov    rdx,QWORD PTR [rsp+0x90]
   2615b:	movups xmm0,XMMWORD PTR [rsp+0x70]
   26160:	movups xmm1,XMMWORD PTR [rsp+0x80]
   26168:	movups XMMWORD PTR [r15+0x10],xmm1
   2616d:	movups XMMWORD PTR [r15],xmm0
   26171:	inc    rdx
   26174:	mov    QWORD PTR [r14+0x28],rdx
   26178:	mov    QWORD PTR [r14+0x50],0x1
   26180:	mov    eax,0x1
   26185:	xor    edi,edi
   26187:	mov    ecx,DWORD PTR [r15+rdi*1]
   2618b:	and    ecx,esi
   2618d:	cmp    ecx,0x7fffffff
   26193:	jne    261bd <diagnostic::kernels::state_only_hiding::measure_qm31+0x47d>
   26195:	dec    rbp
   26198:	jne    260a0 <diagnostic::kernels::state_only_hiding::measure_qm31+0x360>
   2619e:	mov    rdx,QWORD PTR [rsp+0x8]
   261a3:	mov    BYTE PTR [rdx+0x1],0x2
   261a7:	mov    al,0x1
   261a9:	mov    BYTE PTR [rdx],al
   261ab:	add    rsp,0x98
   261b2:	pop    rbx
   261b3:	pop    r12
   261b5:	pop    r13
   261b7:	pop    r14
   261b9:	pop    r15
   261bb:	pop    rbp
   261bc:	ret
   261bd:	mov    rdx,QWORD PTR [rsp+0x8]
   261c2:	mov    DWORD PTR [rdx+0x4],r13d
   261c6:	mov    DWORD PTR [rdx+0x8],r12d
   261ca:	mov    DWORD PTR [rdx+0xc],ebx
   261cd:	mov    DWORD PTR [rdx+0x10],ecx
   261d0:	xor    eax,eax
   261d2:	jmp    261a9 <diagnostic::kernels::state_only_hiding::measure_qm31+0x469>
   261d4:	lea    rsi,[rdi+0x4]
   261d8:	lea    rcx,[rip+0x44a91]        # 6ac70 <__frame_dummy_init_array_entry+0xe0>
   261df:	mov    edx,0x20
   261e4:	call   QWORD PTR [rip+0x46bb6]        # 6cda0 <_DYNAMIC+0x2b8>
   261ea:	int3
   261eb:	int3
   261ec:	int3
   261ed:	int3
   261ee:	int3
   261ef:	int3

0000000000027340 <aspis_prover::host_hashv>:
   27340:	push   rbp
   27341:	push   r15
   27343:	push   r14
   27345:	push   r13
   27347:	push   r12
   27349:	push   rbx
   2734a:	sub    rsp,0x138
   27351:	mov    QWORD PTR [rsp+0x70],rdi
   27356:	xorps  xmm0,xmm0
   27359:	movups XMMWORD PTR [rsp+0x58],xmm0
   2735e:	movups XMMWORD PTR [rsp+0x48],xmm0
   27363:	movups XMMWORD PTR [rsp+0x38],xmm0
   27368:	movups XMMWORD PTR [rsp+0x28],xmm0
   2736d:	mov    BYTE PTR [rsp+0x68],0x0
   27372:	movups xmm0,XMMWORD PTR [rip+0xffffffffffff1757]        # 18ad0 <anon.4542838882158fab56838ae26b7212f7.176.llvm.13126917640099348842>
   27379:	movaps XMMWORD PTR [rsp],xmm0
   2737d:	movups xmm0,XMMWORD PTR [rip+0xffffffffffff175c]        # 18ae0 <anon.4542838882158fab56838ae26b7212f7.176.llvm.13126917640099348842+0x10>
   27384:	movaps XMMWORD PTR [rsp+0x10],xmm0
   27389:	mov    QWORD PTR [rsp+0x20],0x0
   27392:	test   rdx,rdx
   27395:	je     274a4 <aspis_prover::host_hashv+0x164>
   2739b:	mov    r14,rdx
   2739e:	mov    r15,rsi
   273a1:	shl    r14,0x4
   273a5:	add    r14,rsi
   273a8:	xor    r12d,r12d
   273ab:	jmp    273dd <aspis_prover::host_hashv+0x9d>
   273ad:	nop    DWORD PTR [rax]
   273b0:	lea    rax,[rsp+0x28]
   273b5:	lea    rdi,[rax+r13*1]
   273b9:	mov    rsi,rbx
   273bc:	mov    rdx,rbp
   273bf:	call   QWORD PTR [rip+0x45a13]        # 6cdd8 <memcpy@GLIBC_2.14>
   273c5:	add    rbp,r13
   273c8:	mov    r12,rbp
   273cb:	mov    BYTE PTR [rsp+0x68],r12b
   273d0:	add    r15,0x10
   273d4:	cmp    r15,r14
   273d7:	je     274a4 <aspis_prover::host_hashv+0x164>
   273dd:	mov    rbx,QWORD PTR [r15]
   273e0:	mov    rbp,QWORD PTR [r15+0x8]
   273e4:	movzx  r13d,r12b
   273e8:	mov    edx,0x40
   273ed:	sub    rdx,r13
   273f0:	mov    r12,rbp
   273f3:	sub    r12,rdx
   273f6:	jb     273b0 <aspis_prover::host_hashv+0x70>
   273f8:	test   r13,r13
   273fb:	je     27499 <aspis_prover::host_hashv+0x159>
   27401:	lea    rax,[rbx+rdx*1]
   27405:	mov    QWORD PTR [rsp+0x78],rax
   2740a:	mov    rbp,r14
   2740d:	lea    r14,[rsp+0x28]
   27412:	add    r13,r14
   27415:	mov    rdi,r13
   27418:	mov    rsi,rbx
   2741b:	call   QWORD PTR [rip+0x459b7]        # 6cdd8 <memcpy@GLIBC_2.14>
   27421:	inc    QWORD PTR [rsp+0x20]
   27426:	mov    edx,0x1
   2742b:	mov    rdi,rsp
   2742e:	mov    rsi,r14
   27431:	mov    r14,rbp
   27434:	call   QWORD PTR [rip+0x459d6]        # 6ce10 <_DYNAMIC+0x328>
   2743a:	mov    rbx,QWORD PTR [rsp+0x78]
   2743f:	cmp    r12,0x40
   27443:	jb     2745d <aspis_prover::host_hashv+0x11d>
   27445:	mov    rdx,r12
   27448:	shr    rdx,0x6
   2744c:	add    QWORD PTR [rsp+0x20],rdx
   27451:	mov    rdi,rsp
   27454:	mov    rsi,rbx
   27457:	call   QWORD PTR [rip+0x459b3]        # 6ce10 <_DYNAMIC+0x328>
   2745d:	mov    rax,r12
   27460:	movabs rcx,0x7fffffffffffffc0
   2746a:	and    rax,rcx
   2746d:	and    r12d,0x3f
   27471:	add    rbx,rax
   27474:	lea    rdi,[rsp+0x28]
   27479:	mov    rsi,rbx
   2747c:	mov    rdx,r12
   2747f:	call   QWORD PTR [rip+0x45953]        # 6cdd8 <memcpy@GLIBC_2.14>
   27485:	mov    BYTE PTR [rsp+0x68],r12b
   2748a:	add    r15,0x10
   2748e:	cmp    r15,r14
   27491:	jne    273dd <aspis_prover::host_hashv+0x9d>
   27497:	jmp    274a4 <aspis_prover::host_hashv+0x164>
   27499:	mov    r12,rbp
   2749c:	cmp    r12,0x40
   274a0:	jae    27445 <aspis_prover::host_hashv+0x105>
   274a2:	jmp    2745d <aspis_prover::host_hashv+0x11d>
   274a4:	mov    rax,QWORD PTR [rsp+0x60]
   274a9:	mov    QWORD PTR [rsp+0xe0],rax
   274b1:	movzx  eax,BYTE PTR [rsp+0x68]
   274b6:	mov    BYTE PTR [rsp+0xe8],al
   274bd:	mov    eax,DWORD PTR [rsp+0x69]
   274c1:	mov    DWORD PTR [rsp+0xe9],eax
   274c8:	movzx  eax,WORD PTR [rsp+0x6d]
   274cd:	mov    WORD PTR [rsp+0xed],ax
   274d5:	movzx  eax,BYTE PTR [rsp+0x6f]
   274da:	mov    BYTE PTR [rsp+0xef],al
   274e1:	movdqa xmm0,XMMWORD PTR [rsp]
   274e6:	movaps xmm1,XMMWORD PTR [rsp+0x10]
   274eb:	mov    rax,QWORD PTR [rsp+0x20]
   274f0:	mov    rcx,QWORD PTR [rsp+0x28]
   274f5:	movaps xmm2,XMMWORD PTR [rsp+0x30]
   274fa:	mov    QWORD PTR [rsp+0xa0],rax
   27502:	mov    QWORD PTR [rsp+0xa8],rcx
   2750a:	movaps xmm3,XMMWORD PTR [rsp+0x50]
   2750f:	movaps XMMWORD PTR [rsp+0xd0],xmm3
   27517:	movaps xmm3,XMMWORD PTR [rsp+0x40]
   2751c:	movaps XMMWORD PTR [rsp+0xc0],xmm3
   27524:	movaps XMMWORD PTR [rsp+0xb0],xmm2
   2752c:	movaps XMMWORD PTR [rsp+0x90],xmm1
   27534:	movdqa XMMWORD PTR [rsp+0x80],xmm0
   2753d:	lea    rbx,[rsp+0xa8]
   27545:	movzx  r14d,BYTE PTR [rsp+0xe8]
   2754e:	mov    rax,QWORD PTR [rsp+0xa0]
   27556:	shl    rax,0x9
   2755a:	lea    r15d,[r14*8+0x0]
   27562:	or     r15,rax
   27565:	bswap  r15
   27568:	mov    BYTE PTR [rsp+r14*1+0xa8],0x80
   27571:	cmp    r14d,0x3f
   27575:	je     2759e <aspis_prover::host_hashv+0x25e>
   27577:	lea    rdi,[rsp+r14*1]
   2757b:	add    rdi,0xa8
   27582:	inc    rdi
   27585:	mov    rdx,r14
   27588:	xor    rdx,0x3f
   2758c:	xor    esi,esi
   2758e:	call   QWORD PTR [rip+0x45884]        # 6ce18 <memset@GLIBC_2.2.5>
   27594:	xor    r14d,0x38
   27598:	cmp    r14d,0x7
   2759c:	ja     27603 <aspis_prover::host_hashv+0x2c3>
   2759e:	mov    r12,QWORD PTR [rip+0x4586b]        # 6ce10 <_DYNAMIC+0x328>
   275a5:	lea    r14,[rsp+0x80]
   275ad:	mov    edx,0x1
   275b2:	mov    rdi,r14
   275b5:	mov    rsi,rbx
   275b8:	call   r12
   275bb:	pxor   xmm0,xmm0
   275bf:	movdqa XMMWORD PTR [rsp+0x110],xmm0
   275c8:	movdqa XMMWORD PTR [rsp+0x100],xmm0
   275d1:	movdqa XMMWORD PTR [rsp+0xf0],xmm0
   275da:	mov    QWORD PTR [rsp+0x120],0x0
   275e6:	mov    QWORD PTR [rsp+0x128],r15
   275ee:	lea    rsi,[rsp+0xf0]
   275f6:	mov    edx,0x1
   275fb:	mov    rdi,r14
   275fe:	call   r12
   27601:	jmp    27621 <aspis_prover::host_hashv+0x2e1>
   27603:	mov    QWORD PTR [rsp+0xe0],r15
   2760b:	lea    rdi,[rsp+0x80]
   27613:	mov    edx,0x1
   27618:	mov    rsi,rbx
   2761b:	call   QWORD PTR [rip+0x457ef]        # 6ce10 <_DYNAMIC+0x328>
   27621:	pxor   xmm0,xmm0
   27625:	movdqa xmm1,XMMWORD PTR [rsp+0x80]
   2762e:	movdqa xmm2,XMMWORD PTR [rsp+0x90]
   27637:	movdqa xmm3,xmm1
   2763b:	punpckhbw xmm3,xmm0
   2763f:	pshuflw xmm3,xmm3,0x1b
   27644:	pshufhw xmm3,xmm3,0x1b
   27649:	punpcklbw xmm1,xmm0
   2764d:	pshuflw xmm1,xmm1,0x1b
   27652:	pshufhw xmm1,xmm1,0x1b
   27657:	packuswb xmm1,xmm3
   2765b:	movdqa xmm3,xmm2
   2765f:	punpckhbw xmm3,xmm0
   27663:	pshuflw xmm3,xmm3,0x1b
   27668:	pshufhw xmm3,xmm3,0x1b
   2766d:	punpcklbw xmm2,xmm0
   27671:	pshuflw xmm0,xmm2,0x1b
   27676:	pshufhw xmm0,xmm0,0x1b
   2767b:	packuswb xmm0,xmm3
   2767f:	mov    rax,QWORD PTR [rsp+0x70]
   27684:	movdqu XMMWORD PTR [rax],xmm1
   27688:	movdqu XMMWORD PTR [rax+0x10],xmm0
   2768d:	add    rsp,0x138
   27694:	pop    rbx
   27695:	pop    r12
   27697:	pop    r13
   27699:	pop    r14
   2769b:	pop    r15
   2769d:	pop    rbp
   2769e:	ret
   2769f:	int3

00000000000276a0 <sha2::sha256::compress256>:
   276a0:	push   rbp
   276a1:	push   r15
   276a3:	push   r14
   276a5:	push   r13
   276a7:	push   r12
   276a9:	push   rbx
   276aa:	sub    rsp,0x138
   276b1:	mov    rbx,rsi
   276b4:	mov    QWORD PTR [rsp+0xe8],rdi
   276bc:	movzx  eax,BYTE PTR [rip+0x46f3d]        # 6e600 <sha2::sha256::x86::shani_cpuid::STORAGE>
   276c3:	cmp    al,0x1
   276c5:	je     2a2a1 <sha2::sha256::compress256+0x2c01>
   276cb:	movzx  eax,al
   276ce:	cmp    eax,0xff
   276d3:	je     2a28e <sha2::sha256::compress256+0x2bee>
   276d9:	mov    rax,QWORD PTR [rsp+0xe8]
   276e1:	mov    r12d,DWORD PTR [rax]
   276e4:	mov    r14d,DWORD PTR [rax+0x4]
   276e8:	mov    ecx,DWORD PTR [rax+0x8]
   276eb:	mov    QWORD PTR [rsp+0xd0],rcx
   276f3:	mov    ecx,DWORD PTR [rax+0xc]
   276f6:	mov    QWORD PTR [rsp+0xd8],rcx
   276fe:	mov    ebp,DWORD PTR [rax+0x10]
   27701:	mov    r13d,DWORD PTR [rax+0x14]
   27705:	mov    r15d,DWORD PTR [rax+0x18]
   27709:	mov    r9d,DWORD PTR [rax+0x1c]
   2770d:	test   rdx,rdx
   27710:	je     2a235 <sha2::sha256::compress256+0x2b95>
   27716:	shl    rdx,0x6
   2771a:	add    rdx,rbx
   2771d:	mov    QWORD PTR [rsp+0x108],rdx
   27725:	data16 cs nop WORD PTR [rax+rax*1+0x0]
   27730:	mov    QWORD PTR [rsp+0x120],r14
   27738:	mov    edi,r9d
   2773b:	mov    DWORD PTR [rsp+0xe4],r9d
   27743:	mov    eax,DWORD PTR [rbx]
   27745:	mov    ecx,DWORD PTR [rbx+0x4]
   27748:	bswap  eax
   2774a:	mov    rsi,rax
   2774d:	mov    eax,ebp
   2774f:	rol    eax,0x1a
   27752:	bswap  ecx
   27754:	mov    r8,rcx
   27757:	mov    QWORD PTR [rsp+0x60],rcx
   2775c:	mov    ecx,ebp
   2775e:	rol    ecx,0x15
   27761:	xor    ecx,eax
   27763:	mov    eax,ebp
   27765:	rol    eax,0x7
   27768:	xor    eax,ecx
   2776a:	mov    r9,r15
   2776d:	mov    QWORD PTR [rsp+0x110],r15
   27775:	mov    edx,r9d
   27778:	mov    QWORD PTR [rsp+0x128],r13
   27780:	xor    edx,r13d
   27783:	and    edx,ebp
   27785:	xor    edx,r9d
   27788:	add    edx,edi
   2778a:	add    edx,eax
   2778c:	mov    QWORD PTR [rsp+0x48],rsi
   27791:	lea    ecx,[rsi+rdx*1]
   27794:	add    ecx,0x428a2f98
   2779a:	mov    eax,r12d
   2779d:	rol    eax,0x1e
   277a0:	add    edx,esi
   277a2:	mov    esi,r12d
   277a5:	rol    esi,0x13
   277a8:	xor    esi,eax
   277aa:	mov    eax,r12d
   277ad:	rol    eax,0xa
   277b0:	xor    eax,esi
   277b2:	mov    r10,QWORD PTR [rsp+0xd0]
   277ba:	mov    QWORD PTR [rsp+0xd0],r10
   277c2:	mov    esi,r10d
   277c5:	xor    esi,r14d
   277c8:	and    esi,r12d
   277cb:	mov    edi,r10d
   277ce:	and    edi,r14d
   277d1:	xor    edi,esi
   277d3:	add    edi,eax
   277d5:	mov    rax,QWORD PTR [rsp+0xd8]
   277dd:	mov    QWORD PTR [rsp+0xd8],rax
   277e5:	add    eax,edx
   277e7:	add    eax,0x428a2f98
   277ec:	mov    edx,eax
   277ee:	rol    edx,0x1a
   277f1:	add    edi,ecx
   277f3:	mov    ecx,eax
   277f5:	rol    ecx,0x15
   277f8:	xor    ecx,edx
   277fa:	mov    edx,eax
   277fc:	rol    edx,0x7
   277ff:	xor    edx,ecx
   27801:	mov    ecx,r13d
   27804:	xor    ecx,ebp
   27806:	and    ecx,eax
   27808:	xor    ecx,r13d
   2780b:	add    ecx,r15d
   2780e:	add    ecx,r8d
   27811:	lea    esi,[rcx+rdx*1]
   27814:	add    ecx,edx
   27816:	add    ecx,0x71374491
   2781c:	mov    edx,edi
   2781e:	rol    edx,0x1e
   27821:	mov    r8d,edi
   27824:	rol    r8d,0x13
   27828:	xor    r8d,edx
   2782b:	mov    edx,edi
   2782d:	rol    edx,0xa
   27830:	xor    edx,r8d
   27833:	mov    r8d,r14d
   27836:	and    r8d,r12d
   27839:	mov    r9d,r14d
   2783c:	xor    r9d,r12d
   2783f:	and    r9d,edi
   27842:	xor    r9d,r8d
   27845:	add    r9d,edx
   27848:	add    r9d,ecx
   2784b:	lea    ecx,[r10+rsi*1]
   2784f:	add    ecx,0x71374491
   27855:	mov    edx,ecx
   27857:	rol    edx,0x1a
   2785a:	mov    esi,ecx
   2785c:	rol    esi,0x15
   2785f:	xor    esi,edx
   27861:	mov    r8d,ecx
   27864:	rol    r8d,0x7
   27868:	xor    r8d,esi
   2786b:	mov    r15,rbx
   2786e:	mov    edx,DWORD PTR [rbx+0x8]
   27871:	bswap  edx
   27873:	mov    QWORD PTR [rsp+0x88],rdx
   2787b:	mov    esi,eax
   2787d:	xor    esi,ebp
   2787f:	and    esi,ecx
   27881:	xor    esi,ebp
   27883:	add    esi,r13d
   27886:	add    esi,edx
   27888:	mov    r10d,r9d
   2788b:	rol    r10d,0x1e
   2788f:	lea    ebx,[rsi+r8*1]
   27893:	add    esi,r8d
   27896:	add    esi,0xb5c0fbcf
   2789c:	mov    r8d,r9d
   2789f:	rol    r8d,0x13
   278a3:	xor    r8d,r10d
   278a6:	mov    r10d,r9d
   278a9:	rol    r10d,0xa
   278ad:	xor    r10d,r8d
   278b0:	mov    r8d,edi
   278b3:	mov    rdx,r12
   278b6:	xor    r8d,edx
   278b9:	and    r8d,r9d
   278bc:	mov    r11d,edi
   278bf:	and    r11d,edx
   278c2:	mov    QWORD PTR [rsp+0x118],r12
   278ca:	xor    r11d,r8d
   278cd:	add    r11d,r10d
   278d0:	lea    r10d,[r14+rbx*1]
   278d4:	add    r10d,0xb5c0fbcf
   278db:	mov    r8d,r10d
   278de:	rol    r8d,0x1a
   278e2:	add    r11d,esi
   278e5:	mov    esi,r10d
   278e8:	rol    esi,0x15
   278eb:	xor    esi,r8d
   278ee:	mov    r8d,r10d
   278f1:	rol    r8d,0x7
   278f5:	xor    r8d,esi
   278f8:	mov    esi,DWORD PTR [r15+0xc]
   278fc:	mov    r13,r15
   278ff:	bswap  esi
   27901:	mov    QWORD PTR [rsp+0x78],rsi
   27906:	mov    ebx,ecx
   27908:	xor    ebx,eax
   2790a:	and    ebx,r10d
   2790d:	xor    ebx,eax
   2790f:	mov    QWORD PTR [rsp+0x130],rbp
   27917:	add    ebp,esi
   27919:	add    ebx,ebp
   2791b:	mov    r14d,r11d
   2791e:	rol    r14d,0x1e
   27922:	mov    r15d,r11d
   27925:	rol    r15d,0x13
   27929:	lea    r12d,[rbx+r8*1]
   2792d:	add    r8d,ebx
   27930:	add    r8d,0xe9b5dba5
   27937:	mov    ebp,r11d
   2793a:	rol    ebp,0xa
   2793d:	xor    r15d,r14d
   27940:	xor    ebp,r15d
   27943:	mov    ebx,r9d
   27946:	and    ebx,edi
   27948:	mov    r15d,r9d
   2794b:	xor    r15d,edi
   2794e:	and    r15d,r11d
   27951:	xor    r15d,ebx
   27954:	lea    ebx,[rdx+r12*1]
   27958:	add    ebx,0xe9b5dba5
   2795e:	mov    r14d,ebx
   27961:	rol    r14d,0x1a
   27965:	add    r15d,ebp
   27968:	mov    ebp,ebx
   2796a:	rol    ebp,0x15
   2796d:	add    r15d,r8d
   27970:	mov    r8d,ebx
   27973:	rol    r8d,0x7
   27977:	xor    ebp,r14d
   2797a:	xor    r8d,ebp
   2797d:	mov    edx,DWORD PTR [r13+0x10]
   27981:	bswap  edx
   27983:	mov    DWORD PTR [rsp+0x58],edx
   27987:	mov    ebp,r10d
   2798a:	xor    ebp,ecx
   2798c:	and    ebp,ebx
   2798e:	xor    ebp,ecx
   27990:	add    eax,edx
   27992:	mov    r14d,r15d
   27995:	rol    r14d,0x1e
   27999:	add    eax,ebp
   2799b:	mov    ebp,r15d
   2799e:	rol    ebp,0x13
   279a1:	add    eax,r8d
   279a4:	add    eax,0x3956c25b
   279a9:	mov    r12d,r15d
   279ac:	rol    r12d,0xa
   279b0:	xor    ebp,r14d
   279b3:	xor    r12d,ebp
   279b6:	mov    ebp,r11d
   279b9:	xor    ebp,r9d
   279bc:	and    ebp,r15d
   279bf:	mov    r8d,r11d
   279c2:	and    r8d,r9d
   279c5:	xor    r8d,ebp
   279c8:	add    edi,eax
   279ca:	mov    ebp,edi
   279cc:	rol    ebp,0x1a
   279cf:	add    r8d,r12d
   279d2:	mov    r14d,edi
   279d5:	rol    r14d,0x15
   279d9:	add    r8d,eax
   279dc:	mov    eax,edi
   279de:	rol    eax,0x7
   279e1:	xor    r14d,ebp
   279e4:	xor    eax,r14d
   279e7:	mov    edx,DWORD PTR [r13+0x14]
   279eb:	bswap  edx
   279ed:	mov    QWORD PTR [rsp+0x50],rdx
   279f2:	add    ecx,edx
   279f4:	mov    r14d,ebx
   279f7:	xor    r14d,r10d
   279fa:	and    r14d,edi
   279fd:	xor    r14d,r10d
   27a00:	mov    ebp,r8d
   27a03:	rol    ebp,0x1e
   27a06:	add    r14d,ecx
   27a09:	mov    ecx,r8d
   27a0c:	rol    ecx,0x13
   27a0f:	add    eax,r14d
   27a12:	add    eax,0x59f111f1
   27a17:	mov    r14d,r8d
   27a1a:	rol    r14d,0xa
   27a1e:	xor    ecx,ebp
   27a20:	xor    r14d,ecx
   27a23:	mov    ecx,r15d
   27a26:	and    ecx,r11d
   27a29:	mov    r12d,r15d
   27a2c:	xor    r12d,r11d
   27a2f:	and    r12d,r8d
   27a32:	xor    r12d,ecx
   27a35:	add    r9d,eax
   27a38:	mov    ecx,r9d
   27a3b:	rol    ecx,0x1a
   27a3e:	add    r12d,r14d
   27a41:	mov    ebp,r9d
   27a44:	rol    ebp,0x15
   27a47:	add    r12d,eax
   27a4a:	mov    eax,r9d
   27a4d:	rol    eax,0x7
   27a50:	xor    ebp,ecx
   27a52:	xor    eax,ebp
   27a54:	mov    ecx,DWORD PTR [r13+0x18]
   27a58:	bswap  ecx
   27a5a:	mov    QWORD PTR [rsp+0x38],rcx
   27a5f:	add    ecx,r10d
   27a62:	mov    r10d,edi
   27a65:	xor    r10d,ebx
   27a68:	and    r10d,r9d
   27a6b:	xor    r10d,ebx
   27a6e:	mov    ebp,r12d
   27a71:	rol    ebp,0x1e
   27a74:	add    r10d,ecx
   27a77:	mov    ecx,r12d
   27a7a:	rol    ecx,0x13
   27a7d:	add    r10d,eax
   27a80:	add    r10d,0x923f82a4
   27a87:	mov    r14d,r12d
   27a8a:	rol    r14d,0xa
   27a8e:	xor    ecx,ebp
   27a90:	xor    r14d,ecx
   27a93:	mov    ecx,r8d
   27a96:	xor    ecx,r15d
   27a99:	and    ecx,r12d
   27a9c:	mov    eax,r8d
   27a9f:	and    eax,r15d
   27aa2:	xor    eax,ecx
   27aa4:	add    r11d,r10d
   27aa7:	mov    ecx,r11d
   27aaa:	rol    ecx,0x1a
   27aad:	add    eax,r14d
   27ab0:	mov    ebp,r11d
   27ab3:	rol    ebp,0x15
   27ab6:	add    eax,r10d
   27ab9:	mov    r10d,r11d
   27abc:	rol    r10d,0x7
   27ac0:	xor    ebp,ecx
   27ac2:	xor    r10d,ebp
   27ac5:	mov    ecx,DWORD PTR [r13+0x1c]
   27ac9:	bswap  ecx
   27acb:	mov    QWORD PTR [rsp+0xb0],rcx
   27ad3:	add    ecx,ebx
   27ad5:	mov    ebx,r9d
   27ad8:	xor    ebx,edi
   27ada:	and    ebx,r11d
   27add:	xor    ebx,edi
   27adf:	mov    ebp,eax
   27ae1:	rol    ebp,0x1e
   27ae4:	add    ebx,ecx
   27ae6:	mov    r14d,eax
   27ae9:	rol    r14d,0x13
   27aed:	lea    ecx,[r10+rbx*1]
   27af1:	add    ecx,0xab1c5ed5
   27af7:	mov    r10d,eax
   27afa:	rol    r10d,0xa
   27afe:	xor    r14d,ebp
   27b01:	xor    r10d,r14d
   27b04:	mov    ebp,r12d
   27b07:	and    ebp,r8d
   27b0a:	mov    esi,r12d
   27b0d:	xor    esi,r8d
   27b10:	and    esi,eax
   27b12:	xor    esi,ebp
   27b14:	add    r15d,ecx
   27b17:	mov    ebp,r15d
   27b1a:	rol    ebp,0x1a
   27b1d:	add    esi,r10d
   27b20:	mov    r10d,r15d
   27b23:	rol    r10d,0x15
   27b27:	add    esi,ecx
   27b29:	mov    ecx,r15d
   27b2c:	rol    ecx,0x7
   27b2f:	xor    r10d,ebp
   27b32:	xor    ecx,r10d
   27b35:	mov    rbx,r13
   27b38:	mov    edx,DWORD PTR [r13+0x20]
   27b3c:	bswap  edx
   27b3e:	mov    DWORD PTR [rsp+0xa8],edx
   27b45:	add    edi,edx
   27b47:	mov    r10d,r11d
   27b4a:	xor    r10d,r9d
   27b4d:	and    r10d,r15d
   27b50:	xor    r10d,r9d
   27b53:	mov    ebp,esi
   27b55:	rol    ebp,0x1e
   27b58:	add    r10d,edi
   27b5b:	mov    edi,esi
   27b5d:	rol    edi,0x13
   27b60:	add    ecx,r10d
   27b63:	add    ecx,0xd807aa98
   27b69:	mov    r14d,esi
   27b6c:	rol    r14d,0xa
   27b70:	xor    edi,ebp
   27b72:	xor    r14d,edi
   27b75:	mov    edi,eax
   27b77:	xor    edi,r12d
   27b7a:	and    edi,esi
   27b7c:	mov    r13d,eax
   27b7f:	and    r13d,r12d
   27b82:	xor    r13d,edi
   27b85:	add    r8d,ecx
   27b88:	mov    edi,r8d
   27b8b:	rol    edi,0x1a
   27b8e:	add    r13d,r14d
   27b91:	mov    ebp,r8d
   27b94:	rol    ebp,0x15
   27b97:	add    r13d,ecx
   27b9a:	mov    ecx,r8d
   27b9d:	rol    ecx,0x7
   27ba0:	xor    ebp,edi
   27ba2:	xor    ecx,ebp
   27ba4:	mov    r10,rbx
   27ba7:	mov    edx,DWORD PTR [rbx+0x24]
   27baa:	bswap  edx
   27bac:	mov    QWORD PTR [rsp+0x20],rdx
   27bb1:	lea    edi,[rdx+r9*1]
   27bb5:	mov    r9d,r15d
   27bb8:	xor    r9d,r11d
   27bbb:	and    r9d,r8d
   27bbe:	xor    r9d,r11d
   27bc1:	mov    ebp,r13d
   27bc4:	rol    ebp,0x1e
   27bc7:	add    r9d,edi
   27bca:	mov    edi,r13d
   27bcd:	rol    edi,0x13
   27bd0:	add    r9d,ecx
   27bd3:	add    r9d,0x12835b01
   27bda:	mov    r14d,r13d
   27bdd:	rol    r14d,0xa
   27be1:	xor    edi,ebp
   27be3:	xor    r14d,edi
   27be6:	mov    edi,esi
   27be8:	and    edi,eax
   27bea:	mov    ebx,esi
   27bec:	xor    ebx,eax
   27bee:	and    ebx,r13d
   27bf1:	xor    ebx,edi
   27bf3:	add    r12d,r9d
   27bf6:	mov    edi,r12d
   27bf9:	rol    edi,0x1a
   27bfc:	add    ebx,r14d
   27bff:	mov    ebp,r12d
   27c02:	rol    ebp,0x15
   27c05:	add    ebx,r9d
   27c08:	mov    r9d,r12d
   27c0b:	rol    r9d,0x7
   27c0f:	xor    ebp,edi
   27c11:	xor    r9d,ebp
   27c14:	mov    ecx,DWORD PTR [r10+0x28]
   27c18:	mov    rdx,r10
   27c1b:	bswap  ecx
   27c1d:	mov    QWORD PTR [rsp+0x8],rcx
   27c22:	lea    edi,[rcx+r11*1]
   27c26:	mov    r11d,r8d
   27c29:	xor    r11d,r15d
   27c2c:	and    r11d,r12d
   27c2f:	xor    r11d,r15d
   27c32:	mov    ebp,ebx
   27c34:	rol    ebp,0x1e
   27c37:	add    r11d,edi
   27c3a:	mov    edi,ebx
   27c3c:	rol    edi,0x13
   27c3f:	add    r9d,r11d
   27c42:	add    r9d,0x243185be
   27c49:	mov    r11d,ebx
   27c4c:	rol    r11d,0xa
   27c50:	xor    edi,ebp
   27c52:	xor    r11d,edi
   27c55:	mov    edi,r13d
   27c58:	xor    edi,esi
   27c5a:	and    edi,ebx
   27c5c:	mov    r14d,r13d
   27c5f:	and    r14d,esi
   27c62:	xor    r14d,edi
   27c65:	add    eax,r9d
   27c68:	mov    edi,eax
   27c6a:	rol    edi,0x1a
   27c6d:	add    r14d,r11d
   27c70:	mov    r11d,eax
   27c73:	rol    r11d,0x15
   27c77:	add    r14d,r9d
   27c7a:	mov    r9d,eax
   27c7d:	rol    r9d,0x7
   27c81:	xor    r11d,edi
   27c84:	xor    r9d,r11d
   27c87:	mov    ecx,DWORD PTR [r10+0x2c]
   27c8b:	bswap  ecx
   27c8d:	mov    QWORD PTR [rsp+0x18],rcx
   27c92:	lea    edi,[rcx+r15*1]
   27c96:	mov    r11d,r12d
   27c99:	xor    r11d,r8d
   27c9c:	and    r11d,eax
   27c9f:	xor    r11d,r8d
   27ca2:	mov    ebp,r14d
   27ca5:	rol    ebp,0x1e
   27ca8:	add    r11d,edi
   27cab:	mov    r15d,r14d
   27cae:	rol    r15d,0x13
   27cb2:	lea    edi,[r9+r11*1]
   27cb6:	add    edi,0x550c7dc3
   27cbc:	mov    r9d,r14d
   27cbf:	rol    r9d,0xa
   27cc3:	xor    r15d,ebp
   27cc6:	xor    r9d,r15d
   27cc9:	mov    r11d,ebx
   27ccc:	and    r11d,r13d
   27ccf:	mov    r10d,ebx
   27cd2:	xor    r10d,r13d
   27cd5:	and    r10d,r14d
   27cd8:	xor    r10d,r11d
   27cdb:	add    esi,edi
   27cdd:	mov    r11d,esi
   27ce0:	rol    r11d,0x1a
   27ce4:	add    r10d,r9d
   27ce7:	mov    r9d,esi
   27cea:	rol    r9d,0x15
   27cee:	add    r10d,edi
   27cf1:	mov    edi,esi
   27cf3:	rol    edi,0x7
   27cf6:	xor    r9d,r11d
   27cf9:	xor    edi,r9d
   27cfc:	mov    QWORD PTR [rsp+0x100],rdx
   27d04:	mov    ecx,DWORD PTR [rdx+0x30]
   27d07:	bswap  ecx
   27d09:	mov    DWORD PTR [rsp],ecx
   27d0c:	add    r8d,ecx
   27d0f:	mov    r9d,eax
   27d12:	xor    r9d,r12d
   27d15:	and    r9d,esi
   27d18:	xor    r9d,r12d
   27d1b:	mov    r11d,r10d
   27d1e:	rol    r11d,0x1e
   27d22:	add    r9d,r8d
   27d25:	mov    r8d,r10d
   27d28:	rol    r8d,0x13
   27d2c:	add    edi,r9d
   27d2f:	add    edi,0x72be5d74
   27d35:	mov    r9d,r10d
   27d38:	rol    r9d,0xa
   27d3c:	xor    r8d,r11d
   27d3f:	xor    r9d,r8d
   27d42:	mov    r8d,r14d
   27d45:	xor    r8d,ebx
   27d48:	and    r8d,r10d
   27d4b:	mov    ecx,r14d
   27d4e:	and    ecx,ebx
   27d50:	xor    ecx,r8d
   27d53:	add    r13d,edi
   27d56:	mov    r8d,r13d
   27d59:	rol    r8d,0x1a
   27d5d:	add    ecx,r9d
   27d60:	mov    r9d,r13d
   27d63:	rol    r9d,0x15
   27d67:	add    ecx,edi
   27d69:	mov    edi,r13d
   27d6c:	rol    edi,0x7
   27d6f:	xor    r9d,r8d
   27d72:	xor    edi,r9d
   27d75:	mov    edx,DWORD PTR [rdx+0x34]
   27d78:	bswap  edx
   27d7a:	mov    QWORD PTR [rsp+0x40],rdx
   27d7f:	lea    r8d,[rdx+r12*1]
   27d83:	mov    r9d,esi
   27d86:	xor    r9d,eax
   27d89:	and    r9d,r13d
   27d8c:	xor    r9d,eax
   27d8f:	mov    r11d,ecx
   27d92:	rol    r11d,0x1e
   27d96:	add    r9d,r8d
   27d99:	mov    r8d,ecx
   27d9c:	rol    r8d,0x13
   27da0:	add    edi,r9d
   27da3:	add    edi,0x80deb1fe
   27da9:	mov    r15d,ecx
   27dac:	rol    r15d,0xa
   27db0:	xor    r8d,r11d
   27db3:	xor    r15d,r8d
   27db6:	mov    r8d,r10d
   27db9:	and    r8d,r14d
   27dbc:	mov    ebp,r10d
   27dbf:	xor    ebp,r14d
   27dc2:	and    ebp,ecx
   27dc4:	xor    ebp,r8d
   27dc7:	add    ebx,edi
   27dc9:	mov    r8d,ebx
   27dcc:	rol    r8d,0x1a
   27dd0:	add    ebp,r15d
   27dd3:	mov    r11d,ebx
   27dd6:	rol    r11d,0x15
   27dda:	add    ebp,edi
   27ddc:	mov    edi,ebx
   27dde:	rol    edi,0x7
   27de1:	xor    r11d,r8d
   27de4:	xor    edi,r11d
   27de7:	mov    rdx,QWORD PTR [rsp+0x100]
   27def:	mov    r8d,DWORD PTR [rdx+0x38]
   27df3:	bswap  r8d
   27df6:	mov    QWORD PTR [rsp+0x28],r8
   27dfb:	add    eax,r8d
   27dfe:	mov    r8d,r13d
   27e01:	xor    r8d,esi
   27e04:	and    r8d,ebx
   27e07:	mov    QWORD PTR [rsp+0x70],rbx
   27e0c:	xor    r8d,esi
   27e0f:	mov    r11d,ebp
   27e12:	rol    r11d,0x1e
   27e16:	add    r8d,eax
   27e19:	mov    eax,ebp
   27e1b:	rol    eax,0x13
   27e1e:	add    edi,r8d
   27e21:	add    edi,0x9bdc06a7
   27e27:	mov    r8d,ebp
   27e2a:	rol    r8d,0xa
   27e2e:	xor    eax,r11d
   27e31:	xor    r8d,eax
   27e34:	mov    eax,ecx
   27e36:	xor    eax,r10d
   27e39:	and    eax,ebp
   27e3b:	mov    r9d,ecx
   27e3e:	and    r9d,r10d
   27e41:	xor    r9d,eax
   27e44:	add    r14d,edi
   27e47:	mov    eax,r14d
   27e4a:	rol    eax,0x1a
   27e4d:	add    r9d,r8d
   27e50:	mov    r8d,r14d
   27e53:	rol    r8d,0x15
   27e57:	add    r9d,edi
   27e5a:	mov    edi,r14d
   27e5d:	rol    edi,0x7
   27e60:	xor    r8d,eax
   27e63:	xor    edi,r8d
   27e66:	mov    r11d,DWORD PTR [rdx+0x3c]
   27e6a:	bswap  r11d
   27e6d:	lea    eax,[r11+rsi*1]
   27e71:	mov    r8d,ebx
   27e74:	xor    r8d,r13d
   27e77:	and    r8d,r14d
   27e7a:	xor    r8d,r13d
   27e7d:	mov    ebx,r9d
   27e80:	rol    ebx,0x1e
   27e83:	add    r8d,eax
   27e86:	mov    eax,r9d
   27e89:	rol    eax,0x13
   27e8c:	add    r8d,edi
   27e8f:	add    r8d,0xc19bf174
   27e96:	mov    r15d,r9d
   27e99:	rol    r15d,0xa
   27e9d:	xor    eax,ebx
   27e9f:	xor    r15d,eax
   27ea2:	mov    eax,ebp
   27ea4:	mov    DWORD PTR [rsp+0x98],ecx
   27eab:	and    eax,ecx
   27ead:	mov    edx,ebp
   27eaf:	xor    edx,ecx
   27eb1:	and    edx,r9d
   27eb4:	xor    edx,eax
   27eb6:	add    edx,r15d
   27eb9:	mov    rcx,rdx
   27ebc:	mov    edx,DWORD PTR [rsp+0x58]
   27ec0:	mov    eax,edx
   27ec2:	rol    eax,0x19
   27ec5:	add    ecx,r8d
   27ec8:	mov    QWORD PTR [rsp+0x10],rcx
   27ecd:	mov    rdi,QWORD PTR [rsp+0x78]
   27ed2:	mov    ebx,edi
   27ed4:	rol    ebx,0x19
   27ed7:	add    r10d,r8d
   27eda:	mov    r8d,edx
   27edd:	mov    ecx,edx
   27edf:	rol    r8d,0xe
   27ee3:	xor    r8d,eax
   27ee6:	mov    eax,edi
   27ee8:	rol    eax,0xe
   27eeb:	xor    eax,ebx
   27eed:	mov    rsi,QWORD PTR [rsp+0x88]
   27ef5:	mov    ebx,esi
   27ef7:	rol    ebx,0x19
   27efa:	mov    r15d,esi
   27efd:	rol    r15d,0xe
   27f01:	xor    r15d,ebx
   27f04:	mov    rdx,QWORD PTR [rsp+0x60]
   27f09:	mov    ebx,edx
   27f0b:	rol    ebx,0x19
   27f0e:	mov    r12d,edx
   27f11:	rol    r12d,0xe
   27f15:	xor    r12d,ebx
   27f18:	mov    ebx,ecx
   27f1a:	shr    ebx,0x3
   27f1d:	xor    ebx,r8d
   27f20:	mov    r8d,edi
   27f23:	shr    r8d,0x3
   27f27:	xor    r8d,eax
   27f2a:	mov    eax,esi
   27f2c:	shr    eax,0x3
   27f2f:	xor    eax,r15d
   27f32:	mov    r15d,edx
   27f35:	shr    r15d,0x3
   27f39:	xor    r15d,r12d
   27f3c:	add    edi,DWORD PTR [rsp]
   27f3f:	add    edi,ebx
   27f41:	add    esi,DWORD PTR [rsp+0x18]
   27f45:	add    esi,r8d
   27f48:	mov    rcx,rsi
   27f4b:	add    edx,DWORD PTR [rsp+0x8]
   27f4f:	add    edx,eax
   27f51:	mov    r12,rdx
   27f54:	mov    rsi,QWORD PTR [rsp+0x28]
   27f59:	mov    eax,esi
   27f5b:	rol    eax,0xf
   27f5e:	mov    rdx,QWORD PTR [rsp+0x48]
   27f63:	add    edx,DWORD PTR [rsp+0x20]
   27f67:	mov    r8d,esi
   27f6a:	rol    r8d,0xd
   27f6e:	add    edx,r15d
   27f71:	mov    r15,rdx
   27f74:	xor    r8d,eax
   27f77:	mov    edx,esi
   27f79:	shr    edx,0xa
   27f7c:	xor    edx,r8d
   27f7f:	mov    QWORD PTR [rsp+0x80],r11
   27f87:	mov    eax,r11d
   27f8a:	rol    eax,0xf
   27f8d:	add    edx,r15d
   27f90:	mov    r8d,r11d
   27f93:	rol    r8d,0xd
   27f97:	xor    r8d,eax
   27f9a:	shr    r11d,0xa
   27f9e:	xor    r11d,r8d
   27fa1:	add    r11d,r12d
   27fa4:	mov    eax,edx
   27fa6:	rol    eax,0xf
   27fa9:	mov    r8d,edx
   27fac:	rol    r8d,0xd
   27fb0:	xor    r8d,eax
   27fb3:	mov    eax,edx
   27fb5:	mov    ebx,edx
   27fb7:	mov    DWORD PTR [rsp+0x78],edx
   27fbb:	shr    eax,0xa
   27fbe:	xor    eax,r8d
   27fc1:	add    eax,ecx
   27fc3:	mov    r15,rax
   27fc6:	mov    QWORD PTR [rsp+0x48],rax
   27fcb:	mov    eax,r11d
   27fce:	rol    eax,0xf
   27fd1:	mov    edx,r11d
   27fd4:	rol    edx,0xd
   27fd7:	xor    edx,eax
   27fd9:	mov    eax,r11d
   27fdc:	mov    r8,r11
   27fdf:	mov    QWORD PTR [rsp+0x88],r11
   27fe7:	shr    eax,0xa
   27fea:	mov    rcx,rax
   27fed:	mov    eax,r10d
   27ff0:	rol    eax,0x1a
   27ff3:	xor    ecx,edx
   27ff5:	mov    edx,r10d
   27ff8:	rol    edx,0x15
   27ffb:	add    ecx,edi
   27ffd:	mov    r12,rcx
   28000:	mov    QWORD PTR [rsp+0x60],rcx
   28005:	mov    esi,r10d
   28008:	rol    esi,0x7
   2800b:	xor    edx,eax
   2800d:	xor    esi,edx
   2800f:	add    r13d,ebx
   28012:	mov    eax,r14d
   28015:	mov    r11,QWORD PTR [rsp+0x70]
   2801a:	xor    eax,r11d
   2801d:	and    eax,r10d
   28020:	xor    eax,r11d
   28023:	add    eax,r13d
   28026:	add    eax,esi
   28028:	add    eax,0xe49b69c1
   2802d:	mov    rdi,QWORD PTR [rsp+0x10]
   28032:	mov    edx,edi
   28034:	rol    edx,0x1e
   28037:	mov    esi,edi
   28039:	rol    esi,0x13
   2803c:	xor    esi,edx
   2803e:	mov    edx,edi
   28040:	rol    edx,0xa
   28043:	xor    edx,esi
   28045:	mov    esi,r9d
   28048:	xor    esi,ebp
   2804a:	and    esi,edi
   2804c:	mov    ecx,r9d
   2804f:	and    ecx,ebp
   28051:	xor    ecx,esi
   28053:	add    ecx,edx
   28055:	add    ecx,eax
   28057:	mov    esi,ecx
   28059:	mov    r13d,DWORD PTR [rsp+0x98]
   28061:	add    r13d,eax
   28064:	mov    eax,r13d
   28067:	rol    eax,0x1a
   2806a:	mov    edx,r13d
   2806d:	rol    edx,0x15
   28070:	xor    edx,eax
   28072:	mov    eax,r13d
   28075:	rol    eax,0x7
   28078:	xor    eax,edx
   2807a:	lea    ecx,[r8+r11*1]
   2807e:	mov    edx,r10d
   28081:	xor    edx,r14d
   28084:	and    edx,r13d
   28087:	xor    edx,r14d
   2808a:	mov    r8d,esi
   2808d:	rol    esi,0x1e
   28090:	add    edx,ecx
   28092:	mov    ecx,r8d
   28095:	rol    ecx,0x13
   28098:	add    eax,edx
   2809a:	add    eax,0xefbe4786
   2809f:	mov    edx,r8d
   280a2:	mov    r11d,r8d
   280a5:	rol    edx,0xa
   280a8:	xor    ecx,esi
   280aa:	xor    edx,ecx
   280ac:	mov    ecx,edi
   280ae:	and    ecx,r9d
   280b1:	mov    ebx,edi
   280b3:	xor    ebx,r9d
   280b6:	and    ebx,r8d
   280b9:	xor    ebx,ecx
   280bb:	add    ebp,eax
   280bd:	mov    ecx,ebp
   280bf:	rol    ecx,0x1a
   280c2:	add    ebx,edx
   280c4:	mov    edx,ebp
   280c6:	rol    edx,0x15
   280c9:	add    ebx,eax
   280cb:	mov    eax,ebp
   280cd:	rol    eax,0x7
   280d0:	xor    edx,ecx
   280d2:	xor    eax,edx
   280d4:	lea    ecx,[r15+r14*1]
   280d8:	mov    edx,r13d
   280db:	xor    edx,r10d
   280de:	and    edx,ebp
   280e0:	mov    QWORD PTR [rsp+0x68],rbp
   280e5:	xor    edx,r10d
   280e8:	add    edx,ecx
   280ea:	add    eax,edx
   280ec:	add    eax,0xfc19dc6
   280f1:	mov    ecx,ebx
   280f3:	rol    ecx,0x1e
   280f6:	mov    edx,ebx
   280f8:	rol    edx,0x13
   280fb:	xor    edx,ecx
   280fd:	mov    ecx,ebx
   280ff:	rol    ecx,0xa
   28102:	xor    ecx,edx
   28104:	mov    edx,r8d
   28107:	xor    edx,edi
   28109:	and    edx,ebx
   2810b:	mov    esi,r8d
   2810e:	and    esi,edi
   28110:	xor    esi,edx
   28112:	add    esi,ecx
   28114:	add    esi,eax
   28116:	add    r9d,eax
   28119:	mov    eax,r9d
   2811c:	rol    eax,0x1a
   2811f:	mov    ecx,r9d
   28122:	rol    ecx,0x15
   28125:	xor    ecx,eax
   28127:	mov    eax,r9d
   2812a:	mov    QWORD PTR [rsp+0xc0],r9
   28132:	rol    eax,0x7
   28135:	xor    eax,ecx
   28137:	lea    ecx,[r12+r10*1]
   2813b:	mov    edx,ebp
   2813d:	mov    DWORD PTR [rsp+0x98],r13d
   28145:	xor    edx,r13d
   28148:	and    edx,r9d
   2814b:	xor    edx,r13d
   2814e:	mov    r8d,esi
   28151:	rol    r8d,0x1e
   28155:	add    edx,ecx
   28157:	mov    ecx,esi
   28159:	rol    ecx,0x13
   2815c:	lea    ebp,[rax+rdx*1]
   2815f:	add    ebp,0x240ca1cc
   28165:	mov    r14d,esi
   28168:	mov    rdi,rsi
   2816b:	mov    QWORD PTR [rsp+0xa0],rsi
   28173:	rol    r14d,0xa
   28177:	xor    ecx,r8d
   2817a:	mov    esi,DWORD PTR [rsp+0xa8]
   28181:	mov    edx,esi
   28183:	rol    edx,0x19
   28186:	xor    r14d,ecx
   28189:	mov    rcx,QWORD PTR [rsp+0xb0]
   28191:	mov    r12d,ecx
   28194:	rol    r12d,0x19
   28198:	mov    rax,QWORD PTR [rsp+0x38]
   2819d:	mov    r8d,eax
   281a0:	rol    r8d,0x19
   281a4:	mov    DWORD PTR [rsp+0x94],r8d
   281ac:	mov    r15d,ebx
   281af:	mov    DWORD PTR [rsp+0xc8],r11d
   281b7:	and    r15d,r11d
   281ba:	mov    r8,QWORD PTR [rsp+0x50]
   281bf:	mov    r9d,r8d
   281c2:	rol    r9d,0x19
   281c6:	mov    DWORD PTR [rsp+0xb8],r9d
   281ce:	mov    r9d,esi
   281d1:	rol    r9d,0xe
   281d5:	mov    r13d,ebx
   281d8:	xor    r13d,r11d
   281db:	mov    esi,ecx
   281dd:	rol    esi,0xe
   281e0:	mov    r10d,esi
   281e3:	and    r13d,edi
   281e6:	mov    ecx,eax
   281e8:	rol    ecx,0xe
   281eb:	mov    DWORD PTR [rsp+0x70],ecx
   281ef:	xor    r13d,r15d
   281f2:	mov    eax,r8d
   281f5:	rol    eax,0xe
   281f8:	mov    DWORD PTR [rsp+0x34],eax
   281fc:	add    r13d,r14d
   281ff:	mov    eax,DWORD PTR [rsp]
   28202:	mov    esi,eax
   28204:	rol    esi,0x19
   28207:	add    r13d,ebp
   2820a:	mov    rdi,QWORD PTR [rsp+0x18]
   2820f:	mov    ecx,edi
   28211:	rol    ecx,0x19
   28214:	mov    r8,QWORD PTR [rsp+0x10]
   28219:	add    r8d,ebp
   2821c:	mov    QWORD PTR [rsp+0x10],r8
   28221:	mov    r11,QWORD PTR [rsp+0x8]
   28226:	mov    ebp,r11d
   28229:	rol    ebp,0x19
   2822c:	xor    r9d,edx
   2822f:	mov    DWORD PTR [rsp+0xf0],r9d
   28237:	mov    rdx,QWORD PTR [rsp+0x20]
   2823c:	mov    r15d,edx
   2823f:	rol    r15d,0x19
   28243:	xor    r10d,r12d
   28246:	mov    DWORD PTR [rsp+0xfc],r10d
   2824e:	rol    eax,0xe
   28251:	mov    r8d,eax
   28254:	mov    eax,DWORD PTR [rsp+0x94]
   2825b:	xor    DWORD PTR [rsp+0x70],eax
   2825f:	mov    eax,edi
   28261:	rol    eax,0xe
   28264:	mov    edi,DWORD PTR [rsp+0xb8]
   2826b:	xor    DWORD PTR [rsp+0x34],edi
   2826f:	mov    r12d,r11d
   28272:	rol    r12d,0xe
   28276:	xor    r8d,esi
   28279:	mov    DWORD PTR [rsp+0x94],r8d
   28281:	mov    r14d,edx
   28284:	rol    r14d,0xe
   28288:	xor    eax,ecx
   2828a:	mov    DWORD PTR [rsp+0xf8],eax
   28291:	mov    r11d,DWORD PTR [rsp+0x78]
   28296:	mov    ecx,r11d
   28299:	rol    ecx,0x19
   2829c:	xor    r12d,ebp
   2829f:	mov    rbp,QWORD PTR [rsp+0x80]
   282a7:	mov    edx,ebp
   282a9:	rol    edx,0x19
   282ac:	xor    r14d,r15d
   282af:	mov    r15d,r11d
   282b2:	rol    r15d,0xe
   282b6:	xor    r15d,ecx
   282b9:	mov    esi,ebp
   282bb:	rol    esi,0xe
   282be:	xor    esi,edx
   282c0:	mov    r8,QWORD PTR [rsp+0x28]
   282c5:	mov    edx,r8d
   282c8:	rol    edx,0x19
   282cb:	mov    edi,r8d
   282ce:	rol    edi,0xe
   282d1:	xor    edi,edx
   282d3:	mov    r9,QWORD PTR [rsp+0x40]
   282d8:	mov    edx,r9d
   282db:	rol    edx,0x19
   282de:	mov    r10d,r9d
   282e1:	rol    r10d,0xe
   282e5:	xor    r10d,edx
   282e8:	mov    ecx,r11d
   282eb:	shr    ecx,0x3
   282ee:	xor    ecx,r15d
   282f1:	mov    rdx,QWORD PTR [rsp+0x38]
   282f6:	mov    r15d,edx
   282f9:	add    edx,ebp
   282fb:	mov    rax,rbp
   282fe:	add    ecx,eax
   28300:	mov    DWORD PTR [rsp+0xb8],ecx
   28307:	shr    eax,0x3
   2830a:	xor    eax,esi
   2830c:	mov    rbp,QWORD PTR [rsp+0x50]
   28311:	mov    ecx,ebp
   28313:	add    ebp,r8d
   28316:	add    eax,r8d
   28319:	mov    QWORD PTR [rsp+0x80],rax
   28321:	shr    r8d,0x3
   28325:	xor    r8d,edi
   28328:	mov    rax,r9
   2832b:	mov    r9d,DWORD PTR [rsp+0x58]
   28330:	add    r9d,eax
   28333:	add    r8d,eax
   28336:	mov    QWORD PTR [rsp+0x28],r8
   2833b:	shr    eax,0x3
   2833e:	xor    eax,r10d
   28341:	mov    r8d,DWORD PTR [rsp]
   28345:	add    eax,r8d
   28348:	mov    QWORD PTR [rsp+0x40],rax
   2834d:	shr    r8d,0x3
   28351:	xor    r8d,DWORD PTR [rsp+0x94]
   28359:	mov    rax,QWORD PTR [rsp+0x18]
   2835e:	add    r8d,eax
   28361:	mov    DWORD PTR [rsp+0x94],r8d
   28369:	shr    eax,0x3
   2836c:	xor    eax,DWORD PTR [rsp+0xf8]
   28373:	mov    rsi,QWORD PTR [rsp+0x8]
   28378:	add    eax,esi
   2837a:	mov    QWORD PTR [rsp+0x18],rax
   2837f:	shr    esi,0x3
   28382:	xor    esi,r12d
   28385:	mov    rax,QWORD PTR [rsp+0x20]
   2838a:	add    esi,eax
   2838c:	mov    QWORD PTR [rsp+0x8],rsi
   28391:	shr    eax,0x3
   28394:	xor    eax,r14d
   28397:	mov    esi,DWORD PTR [rsp+0xa8]
   2839e:	add    eax,esi
   283a0:	mov    QWORD PTR [rsp+0x20],rax
   283a5:	mov    eax,esi
   283a7:	shr    eax,0x3
   283aa:	xor    eax,DWORD PTR [rsp+0xf0]
   283b1:	mov    rsi,QWORD PTR [rsp+0xb0]
   283b9:	add    eax,esi
   283bb:	shr    esi,0x3
   283be:	xor    esi,DWORD PTR [rsp+0xfc]
   283c5:	shr    r15d,0x3
   283c9:	xor    r15d,DWORD PTR [rsp+0x70]
   283ce:	shr    ecx,0x3
   283d1:	xor    ecx,DWORD PTR [rsp+0x34]
   283d5:	add    edx,esi
   283d7:	mov    r8,QWORD PTR [rsp+0x48]
   283dc:	mov    esi,r8d
   283df:	rol    esi,0xf
   283e2:	add    ebp,r15d
   283e5:	mov    r14d,r8d
   283e8:	rol    r14d,0xd
   283ec:	mov    edi,r9d
   283ef:	add    edi,ecx
   283f1:	xor    r14d,esi
   283f4:	mov    r9d,r8d
   283f7:	shr    r9d,0xa
   283fb:	xor    r9d,r14d
   283fe:	mov    r8,QWORD PTR [rsp+0x60]
   28403:	mov    ecx,r8d
   28406:	rol    ecx,0xf
   28409:	add    r9d,edi
   2840c:	mov    esi,r8d
   2840f:	rol    esi,0xd
   28412:	xor    esi,ecx
   28414:	mov    edi,r8d
   28417:	shr    edi,0xa
   2841a:	xor    edi,esi
   2841c:	add    edi,ebp
   2841e:	mov    ecx,r9d
   28421:	rol    ecx,0xf
   28424:	mov    esi,r9d
   28427:	rol    esi,0xd
   2842a:	xor    esi,ecx
   2842c:	mov    ecx,r9d
   2842f:	mov    DWORD PTR [rsp+0x38],r9d
   28434:	shr    ecx,0xa
   28437:	xor    ecx,esi
   28439:	add    ecx,edx
   2843b:	mov    r12,rcx
   2843e:	mov    ecx,edi
   28440:	rol    ecx,0xf
   28443:	mov    esi,edi
   28445:	rol    esi,0xd
   28448:	xor    esi,ecx
   2844a:	mov    ecx,edi
   2844c:	mov    QWORD PTR [rsp],rdi
   28450:	shr    ecx,0xa
   28453:	xor    ecx,esi
   28455:	add    eax,r11d
   28458:	add    ecx,eax
   2845a:	mov    r10,rcx
   2845d:	mov    rdx,QWORD PTR [rsp+0x10]
   28462:	mov    eax,edx
   28464:	rol    eax,0x1a
   28467:	mov    ecx,edx
   28469:	rol    ecx,0x15
   2846c:	xor    ecx,eax
   2846e:	mov    eax,edx
   28470:	rol    eax,0x7
   28473:	xor    eax,ecx
   28475:	mov    r8d,DWORD PTR [rsp+0x98]
   2847d:	add    r8d,r9d
   28480:	mov    r15,QWORD PTR [rsp+0xc0]
   28488:	mov    ecx,r15d
   2848b:	mov    rsi,QWORD PTR [rsp+0x68]
   28490:	xor    ecx,esi
   28492:	and    ecx,edx
   28494:	xor    ecx,esi
   28496:	mov    r9,rsi
   28499:	add    ecx,r8d
   2849c:	mov    r8,r13
   2849f:	mov    esi,r8d
   284a2:	rol    esi,0x1e
   284a5:	add    ecx,eax
   284a7:	add    ecx,0x2de92c6f
   284ad:	mov    eax,r8d
   284b0:	rol    eax,0x13
   284b3:	xor    eax,esi
   284b5:	mov    esi,r8d
   284b8:	rol    esi,0xa
   284bb:	xor    esi,eax
   284bd:	mov    rbp,QWORD PTR [rsp+0xa0]
   284c5:	mov    r14d,ebp
   284c8:	xor    r14d,ebx
   284cb:	and    r14d,r8d
   284ce:	mov    eax,ebp
   284d0:	and    eax,ebx
   284d2:	xor    eax,r14d
   284d5:	add    eax,esi
   284d7:	mov    r11d,DWORD PTR [rsp+0xc8]
   284df:	add    r11d,ecx
   284e2:	mov    esi,r11d
   284e5:	rol    esi,0x1a
   284e8:	add    eax,ecx
   284ea:	mov    ecx,r11d
   284ed:	rol    ecx,0x15
   284f0:	xor    ecx,esi
   284f2:	mov    esi,r11d
   284f5:	rol    esi,0x7
   284f8:	xor    esi,ecx
   284fa:	lea    ecx,[rdi+r9*1]
   284fe:	mov    r9d,edx
   28501:	mov    rdi,r15
   28504:	xor    r9d,edi
   28507:	and    r9d,r11d
   2850a:	xor    r9d,edi
   2850d:	add    r9d,ecx
   28510:	add    esi,r9d
   28513:	add    esi,0x4a7484aa
   28519:	mov    ecx,eax
   2851b:	rol    ecx,0x1e
   2851e:	mov    r9d,eax
   28521:	rol    r9d,0x13
   28525:	xor    r9d,ecx
   28528:	mov    r14d,eax
   2852b:	rol    r14d,0xa
   2852f:	xor    r14d,r9d
   28532:	mov    r9d,r8d
   28535:	and    r9d,ebp
   28538:	mov    ecx,r8d
   2853b:	xor    ecx,ebp
   2853d:	and    ecx,eax
   2853f:	xor    ecx,r9d
   28542:	add    ecx,r14d
   28545:	add    ecx,esi
   28547:	mov    r15,rbx
   2854a:	add    r15d,esi
   2854d:	mov    esi,r15d
   28550:	rol    esi,0x1a
   28553:	mov    r9d,r15d
   28556:	rol    r9d,0x15
   2855a:	xor    r9d,esi
   2855d:	mov    esi,r15d
   28560:	rol    esi,0x7
   28563:	xor    esi,r9d
   28566:	mov    r14d,r11d
   28569:	xor    r14d,edx
   2856c:	and    r14d,r15d
   2856f:	xor    r14d,edx
   28572:	add    r14d,r12d
   28575:	add    r14d,edi
   28578:	mov    r9d,ecx
   2857b:	rol    r9d,0x1e
   2857f:	add    esi,r14d
   28582:	add    esi,0x5cb0a9dc
   28588:	mov    r14d,ecx
   2858b:	rol    r14d,0x13
   2858f:	xor    r14d,r9d
   28592:	mov    r13d,ecx
   28595:	rol    r13d,0xa
   28599:	xor    r13d,r14d
   2859c:	mov    r14d,eax
   2859f:	xor    r14d,r8d
   285a2:	and    r14d,ecx
   285a5:	mov    r9d,eax
   285a8:	and    r9d,r8d
   285ab:	xor    r9d,r14d
   285ae:	add    r9d,r13d
   285b1:	mov    rbx,rbp
   285b4:	add    ebx,esi
   285b6:	mov    r14d,ebx
   285b9:	rol    r14d,0x1a
   285bd:	add    r9d,esi
   285c0:	mov    esi,ebx
   285c2:	rol    esi,0x15
   285c5:	xor    esi,r14d
   285c8:	mov    r14d,ebx
   285cb:	rol    r14d,0x7
   285cf:	xor    r14d,esi
   285d2:	mov    edi,r15d
   285d5:	xor    edi,r11d
   285d8:	and    edi,ebx
   285da:	xor    edi,r11d
   285dd:	add    edi,r10d
   285e0:	add    edi,edx
   285e2:	lea    esi,[r14+rdi*1]
   285e6:	add    esi,0x76f988da
   285ec:	mov    edi,r9d
   285ef:	rol    edi,0x1e
   285f2:	mov    r14d,r9d
   285f5:	rol    r14d,0x13
   285f9:	xor    r14d,edi
   285fc:	mov    r13d,r9d
   285ff:	rol    r13d,0xa
   28603:	xor    r13d,r14d
   28606:	mov    r14d,ecx
   28609:	and    r14d,eax
   2860c:	mov    edi,ecx
   2860e:	xor    edi,eax
   28610:	and    edi,r9d
   28613:	xor    edi,r14d
   28616:	add    edi,r13d
   28619:	add    edi,esi
   2861b:	add    r8d,esi
   2861e:	mov    QWORD PTR [rsp+0x58],r12
   28623:	mov    esi,r12d
   28626:	rol    esi,0xf
   28629:	mov    r14d,r12d
   2862c:	rol    r14d,0xd
   28630:	xor    r14d,esi
   28633:	mov    ebp,r12d
   28636:	shr    ebp,0xa
   28639:	xor    ebp,r14d
   2863c:	mov    rdx,QWORD PTR [rsp+0x20]
   28641:	add    edx,DWORD PTR [rsp+0x88]
   28648:	add    ebp,edx
   2864a:	mov    rdx,r10
   2864d:	mov    QWORD PTR [rsp+0x50],r10
   28652:	mov    esi,edx
   28654:	rol    esi,0xf
   28657:	mov    r14d,edx
   2865a:	rol    r14d,0xd
   2865e:	xor    r14d,esi
   28661:	shr    edx,0xa
   28664:	xor    edx,r14d
   28667:	mov    rsi,QWORD PTR [rsp+0x8]
   2866c:	add    esi,DWORD PTR [rsp+0x48]
   28670:	add    edx,esi
   28672:	mov    esi,ebp
   28674:	rol    esi,0xf
   28677:	mov    r14d,ebp
   2867a:	rol    r14d,0xd
   2867e:	xor    r14d,esi
   28681:	mov    esi,ebp
   28683:	shr    esi,0xa
   28686:	xor    esi,r14d
   28689:	mov    r10,QWORD PTR [rsp+0x18]
   2868e:	add    r10d,DWORD PTR [rsp+0x60]
   28693:	add    esi,r10d
   28696:	mov    r12,rsi
   28699:	mov    esi,edx
   2869b:	rol    esi,0xf
   2869e:	mov    r14d,edx
   286a1:	rol    r14d,0xd
   286a5:	xor    r14d,esi
   286a8:	mov    r13d,edx
   286ab:	mov    r10,rdx
   286ae:	mov    QWORD PTR [rsp+0x98],rdx
   286b6:	shr    r13d,0xa
   286ba:	xor    r13d,r14d
   286bd:	mov    edx,DWORD PTR [rsp+0x94]
   286c4:	add    edx,DWORD PTR [rsp+0x38]
   286c8:	add    r13d,edx
   286cb:	mov    edx,r8d
   286ce:	rol    edx,0x1a
   286d1:	mov    esi,r8d
   286d4:	rol    esi,0x15
   286d7:	xor    esi,edx
   286d9:	mov    edx,r8d
   286dc:	rol    edx,0x7
   286df:	xor    edx,esi
   286e1:	add    r11d,ebp
   286e4:	mov    DWORD PTR [rsp+0x34],ebp
   286e8:	mov    esi,ebx
   286ea:	xor    esi,r15d
   286ed:	and    esi,r8d
   286f0:	xor    esi,r15d
   286f3:	add    esi,r11d
   286f6:	mov    r11d,edi
   286f9:	rol    r11d,0x1e
   286fd:	add    edx,esi
   286ff:	add    edx,0x983e5152
   28705:	mov    esi,edi
   28707:	rol    esi,0x13
   2870a:	xor    esi,r11d
   2870d:	mov    r14d,edi
   28710:	rol    r14d,0xa
   28714:	xor    r14d,esi
   28717:	mov    esi,r9d
   2871a:	xor    esi,ecx
   2871c:	and    esi,edi
   2871e:	mov    r11d,r9d
   28721:	and    r11d,ecx
   28724:	xor    r11d,esi
   28727:	add    r11d,r14d
   2872a:	add    eax,edx
   2872c:	mov    esi,eax
   2872e:	rol    esi,0x1a
   28731:	add    r11d,edx
   28734:	mov    edx,eax
   28736:	rol    edx,0x15
   28739:	xor    edx,esi
   2873b:	mov    esi,eax
   2873d:	rol    esi,0x7
   28740:	xor    esi,edx
   28742:	lea    edx,[r10+r15*1]
   28746:	mov    r10d,r8d
   28749:	xor    r10d,ebx
   2874c:	and    r10d,eax
   2874f:	xor    r10d,ebx
   28752:	add    r10d,edx
   28755:	lea    edx,[rsi+r10*1]
   28759:	add    edx,0xa831c66d
   2875f:	mov    esi,r11d
   28762:	rol    esi,0x1e
   28765:	mov    r10d,r11d
   28768:	rol    r10d,0x13
   2876c:	xor    r10d,esi
   2876f:	mov    r14d,r11d
   28772:	rol    r14d,0xa
   28776:	xor    r14d,r10d
   28779:	mov    r10d,edi
   2877c:	and    r10d,r9d
   2877f:	mov    r15d,edi
   28782:	xor    r15d,r9d
   28785:	and    r15d,r11d
   28788:	xor    r15d,r10d
   2878b:	add    r15d,r14d
   2878e:	add    r15d,edx
   28791:	add    ecx,edx
   28793:	mov    edx,ecx
   28795:	rol    edx,0x1a
   28798:	mov    r10d,ecx
   2879b:	rol    r10d,0x15
   2879f:	xor    r10d,edx
   287a2:	mov    edx,ecx
   287a4:	rol    edx,0x7
   287a7:	xor    edx,r10d
   287aa:	lea    r10d,[r12+rbx*1]
   287ae:	mov    ebx,eax
   287b0:	xor    ebx,r8d
   287b3:	and    ebx,ecx
   287b5:	xor    ebx,r8d
   287b8:	add    ebx,r10d
   287bb:	mov    r10d,r15d
   287be:	rol    r10d,0x1e
   287c2:	add    edx,ebx
   287c4:	add    edx,0xb00327c8
   287ca:	mov    ebx,r15d
   287cd:	rol    ebx,0x13
   287d0:	xor    ebx,r10d
   287d3:	mov    r10d,r15d
   287d6:	rol    r10d,0xa
   287da:	xor    r10d,ebx
   287dd:	mov    ebx,r11d
   287e0:	xor    ebx,edi
   287e2:	and    ebx,r15d
   287e5:	mov    r14d,r11d
   287e8:	and    r14d,edi
   287eb:	xor    r14d,ebx
   287ee:	add    r14d,r10d
   287f1:	add    r9d,edx
   287f4:	mov    r10d,r9d
   287f7:	rol    r10d,0x1a
   287fb:	add    r14d,edx
   287fe:	mov    edx,r9d
   28801:	rol    edx,0x15
   28804:	xor    edx,r10d
   28807:	mov    r10d,r9d
   2880a:	rol    r10d,0x7
   2880e:	xor    r10d,edx
   28811:	lea    edx,[r8+r13*1]
   28815:	mov    r8d,ecx
   28818:	xor    r8d,eax
   2881b:	and    r8d,r9d
   2881e:	xor    r8d,eax
   28821:	add    r8d,edx
   28824:	lea    edx,[r10+r8*1]
   28828:	add    edx,0xbf597fc7
   2882e:	mov    r8d,r14d
   28831:	rol    r8d,0x1e
   28835:	mov    r10d,r14d
   28838:	rol    r10d,0x13
   2883c:	xor    r10d,r8d
   2883f:	mov    ebx,r14d
   28842:	rol    ebx,0xa
   28845:	xor    ebx,r10d
   28848:	mov    r10d,r15d
   2884b:	and    r10d,r11d
   2884e:	mov    esi,r15d
   28851:	xor    esi,r11d
   28854:	and    esi,r14d
   28857:	xor    esi,r10d
   2885a:	add    esi,ebx
   2885c:	add    esi,edx
   2885e:	mov    rbx,rsi
   28861:	add    edi,edx
   28863:	mov    QWORD PTR [rsp+0x18],r12
   28868:	mov    edx,r12d
   2886b:	rol    edx,0xf
   2886e:	mov    r10d,r12d
   28871:	rol    r10d,0xd
   28875:	xor    r10d,edx
   28878:	mov    esi,r12d
   2887b:	shr    esi,0xa
   2887e:	xor    esi,r10d
   28881:	mov    rdx,QWORD PTR [rsp+0x40]
   28886:	add    edx,DWORD PTR [rsp]
   28889:	add    esi,edx
   2888b:	mov    QWORD PTR [rsp+0xb0],r13
   28893:	mov    edx,r13d
   28896:	rol    edx,0xf
   28899:	mov    r10d,r13d
   2889c:	rol    r10d,0xd
   288a0:	xor    r10d,edx
   288a3:	mov    edx,r13d
   288a6:	mov    r8,rdx
   288a9:	shr    r8d,0xa
   288ad:	xor    r8d,r10d
   288b0:	mov    rdx,QWORD PTR [rsp+0x28]
   288b5:	add    edx,DWORD PTR [rsp+0x58]
   288b9:	add    r8d,edx
   288bc:	mov    edx,esi
   288be:	rol    edx,0xf
   288c1:	mov    r10d,esi
   288c4:	rol    r10d,0xd
   288c8:	xor    r10d,edx
   288cb:	mov    r13d,esi
   288ce:	mov    DWORD PTR [rsp+0xa8],esi
   288d5:	shr    r13d,0xa
   288d9:	xor    r13d,r10d
   288dc:	mov    r10,QWORD PTR [rsp+0x80]
   288e4:	add    r10d,DWORD PTR [rsp+0x50]
   288e9:	add    r13d,r10d
   288ec:	mov    QWORD PTR [rsp+0x10],r13
   288f1:	mov    edx,r8d
   288f4:	rol    edx,0xf
   288f7:	mov    r10d,r8d
   288fa:	rol    r10d,0xd
   288fe:	xor    r10d,edx
   28901:	mov    edx,r8d
   28904:	mov    QWORD PTR [rsp+0x40],r8
   28909:	shr    edx,0xa
   2890c:	xor    edx,r10d
   2890f:	mov    r10d,DWORD PTR [rsp+0xb8]
   28917:	add    r10d,ebp
   2891a:	add    edx,r10d
   2891d:	mov    QWORD PTR [rsp+0x8],rdx
   28922:	mov    edx,edi
   28924:	rol    edx,0x1a
   28927:	mov    r10d,edi
   2892a:	rol    r10d,0x15
   2892e:	xor    r10d,edx
   28931:	mov    edx,edi
   28933:	rol    edx,0x7
   28936:	xor    edx,r10d
   28939:	add    eax,esi
   2893b:	mov    r10d,r9d
   2893e:	xor    r10d,ecx
   28941:	and    r10d,edi
   28944:	xor    r10d,ecx
   28947:	add    r10d,eax
   2894a:	mov    eax,ebx
   2894c:	rol    eax,0x1e
   2894f:	add    edx,r10d
   28952:	add    edx,0xc6e00bf3
   28958:	mov    r10d,ebx
   2895b:	rol    r10d,0x13
   2895f:	xor    r10d,eax
   28962:	mov    eax,ebx
   28964:	mov    rsi,rbx
   28967:	rol    eax,0xa
   2896a:	xor    eax,r10d
   2896d:	mov    ebx,r14d
   28970:	xor    ebx,r15d
   28973:	and    ebx,esi
   28975:	mov    r12d,r14d
   28978:	and    r12d,r15d
   2897b:	xor    r12d,ebx
   2897e:	add    r12d,eax
   28981:	add    r11d,edx
   28984:	mov    eax,r11d
   28987:	rol    eax,0x1a
   2898a:	add    r12d,edx
   2898d:	mov    edx,r11d
   28990:	rol    edx,0x15
   28993:	xor    edx,eax
   28995:	mov    eax,r11d
   28998:	rol    eax,0x7
   2899b:	xor    eax,edx
   2899d:	add    ecx,r8d
   289a0:	mov    edx,edi
   289a2:	xor    edx,r9d
   289a5:	and    edx,r11d
   289a8:	xor    edx,r9d
   289ab:	add    edx,ecx
   289ad:	add    eax,edx
   289af:	add    eax,0xd5a79147
   289b4:	mov    ecx,r12d
   289b7:	rol    ecx,0x1e
   289ba:	mov    edx,r12d
   289bd:	rol    edx,0x13
   289c0:	xor    edx,ecx
   289c2:	mov    ecx,r12d
   289c5:	rol    ecx,0xa
   289c8:	xor    ecx,edx
   289ca:	mov    r10,rsi
   289cd:	mov    ebx,r10d
   289d0:	and    ebx,r14d
   289d3:	mov    ebp,r10d
   289d6:	xor    ebp,r14d
   289d9:	and    ebp,r12d
   289dc:	xor    ebp,ebx
   289de:	add    ebp,ecx
   289e0:	add    ebp,eax
   289e2:	add    r15d,eax
   289e5:	mov    eax,r15d
   289e8:	rol    eax,0x1a
   289eb:	mov    ecx,r15d
   289ee:	rol    ecx,0x15
   289f1:	xor    ecx,eax
   289f3:	mov    eax,r15d
   289f6:	rol    eax,0x7
   289f9:	xor    eax,ecx
   289fb:	lea    ecx,[r9+r13*1]
   289ff:	mov    r9d,r11d
   28a02:	xor    r9d,edi
   28a05:	and    r9d,r15d
   28a08:	xor    r9d,edi
   28a0b:	add    r9d,ecx
   28a0e:	mov    ecx,ebp
   28a10:	rol    ecx,0x1e
   28a13:	add    eax,r9d
   28a16:	add    eax,0x6ca6351
   28a1b:	mov    r9d,ebp
   28a1e:	rol    r9d,0x13
   28a22:	xor    r9d,ecx
   28a25:	mov    ecx,ebp
   28a27:	rol    ecx,0xa
   28a2a:	xor    ecx,r9d
   28a2d:	mov    r9d,r12d
   28a30:	xor    r9d,r10d
   28a33:	and    r9d,ebp
   28a36:	mov    edx,r12d
   28a39:	and    edx,r10d
   28a3c:	xor    edx,r9d
   28a3f:	add    edx,ecx
   28a41:	mov    rsi,rdx
   28a44:	add    r14d,eax
   28a47:	mov    ecx,r14d
   28a4a:	rol    ecx,0x1a
   28a4d:	add    esi,eax
   28a4f:	mov    eax,r14d
   28a52:	rol    eax,0x15
   28a55:	xor    eax,ecx
   28a57:	mov    ecx,r14d
   28a5a:	mov    QWORD PTR [rsp+0x20],r14
   28a5f:	rol    ecx,0x7
   28a62:	xor    ecx,eax
   28a64:	mov    rax,QWORD PTR [rsp+0x8]
   28a69:	add    eax,edi
   28a6b:	mov    edi,r15d
   28a6e:	mov    DWORD PTR [rsp+0x28],r11d
   28a73:	xor    edi,r11d
   28a76:	and    edi,r14d
   28a79:	xor    edi,r11d
   28a7c:	add    edi,eax
   28a7e:	lea    edx,[rcx+rdi*1]
   28a81:	add    edx,0x14292967
   28a87:	mov    ecx,esi
   28a89:	rol    ecx,0x1e
   28a8c:	mov    r9d,esi
   28a8f:	rol    r9d,0x13
   28a93:	xor    r9d,ecx
   28a96:	mov    edi,esi
   28a98:	mov    rcx,rsi
   28a9b:	mov    QWORD PTR [rsp+0x70],rsi
   28aa0:	rol    edi,0xa
   28aa3:	xor    edi,r9d
   28aa6:	mov    r9d,ebp
   28aa9:	and    r9d,r12d
   28aac:	mov    ebx,DWORD PTR [rsp+0x38]
   28ab0:	mov    eax,ebx
   28ab2:	rol    eax,0x19
   28ab5:	mov    r8,QWORD PTR [rsp+0x60]
   28aba:	mov    r14d,r8d
   28abd:	rol    r14d,0x19
   28ac1:	mov    r11d,ebp
   28ac4:	xor    r11d,r12d
   28ac7:	mov    rsi,QWORD PTR [rsp+0x48]
   28acc:	mov    r13d,esi
   28acf:	rol    r13d,0x19
   28ad3:	mov    DWORD PTR [rsp+0x68],r13d
   28ad8:	and    r11d,ecx
   28adb:	mov    rcx,QWORD PTR [rsp+0x88]
   28ae3:	mov    r13d,ecx
   28ae6:	rol    r13d,0x19
   28aea:	mov    DWORD PTR [rsp+0xa0],r13d
   28af2:	xor    r11d,r9d
   28af5:	mov    r9d,ebx
   28af8:	rol    r9d,0xe
   28afc:	add    r11d,edi
   28aff:	mov    edi,r8d
   28b02:	rol    edi,0xe
   28b05:	add    r11d,edx
   28b08:	mov    ebx,esi
   28b0a:	rol    ebx,0xe
   28b0d:	add    r10d,edx
   28b10:	mov    QWORD PTR [rsp+0xc0],r10
   28b18:	mov    edx,ecx
   28b1a:	rol    edx,0xe
   28b1d:	mov    esi,edx
   28b1f:	xor    r9d,eax
   28b22:	mov    DWORD PTR [rsp+0x80],r9d
   28b2a:	mov    r13d,DWORD PTR [rsp+0x34]
   28b2f:	mov    ecx,r13d
   28b32:	rol    ecx,0x19
   28b35:	mov    r10d,edi
   28b38:	xor    r10d,r14d
   28b3b:	mov    rdi,QWORD PTR [rsp+0x50]
   28b40:	mov    edx,edi
   28b42:	rol    edx,0x19
   28b45:	xor    ebx,DWORD PTR [rsp+0x68]
   28b49:	mov    r14,QWORD PTR [rsp+0x58]
   28b4e:	mov    r9d,r14d
   28b51:	rol    r9d,0x19
   28b55:	xor    esi,DWORD PTR [rsp+0xa0]
   28b5c:	mov    DWORD PTR [rsp+0x68],esi
   28b60:	mov    eax,r13d
   28b63:	rol    eax,0xe
   28b66:	xor    eax,ecx
   28b68:	mov    ecx,edi
   28b6a:	rol    ecx,0xe
   28b6d:	xor    ecx,edx
   28b6f:	mov    edx,r14d
   28b72:	rol    edx,0xe
   28b75:	xor    edx,r9d
   28b78:	mov    r8,QWORD PTR [rsp]
   28b7c:	mov    r9d,r8d
   28b7f:	rol    r9d,0x19
   28b83:	mov    esi,r8d
   28b86:	rol    esi,0xe
   28b89:	xor    esi,r9d
   28b8c:	shr    r13d,0x3
   28b90:	xor    r13d,eax
   28b93:	add    r13d,edi
   28b96:	mov    DWORD PTR [rsp+0xa0],r13d
   28b9e:	shr    edi,0x3
   28ba1:	xor    edi,ecx
   28ba3:	mov    rcx,r14
   28ba6:	add    edi,ecx
   28ba8:	mov    QWORD PTR [rsp+0x50],rdi
   28bad:	shr    ecx,0x3
   28bb0:	xor    ecx,edx
   28bb2:	mov    rax,r8
   28bb5:	add    ecx,eax
   28bb7:	mov    QWORD PTR [rsp+0x58],rcx
   28bbc:	shr    eax,0x3
   28bbf:	xor    eax,esi
   28bc1:	mov    r8d,DWORD PTR [rsp+0x38]
   28bc6:	add    eax,r8d
   28bc9:	mov    QWORD PTR [rsp],rax
   28bcd:	shr    r8d,0x3
   28bd1:	xor    r8d,DWORD PTR [rsp+0x80]
   28bd9:	mov    r13,QWORD PTR [rsp+0x60]
   28bde:	add    r8d,r13d
   28be1:	shr    r13d,0x3
   28be5:	xor    r13d,r10d
   28be8:	mov    rcx,QWORD PTR [rsp+0x48]
   28bed:	add    r13d,ecx
   28bf0:	shr    ecx,0x3
   28bf3:	xor    ecx,ebx
   28bf5:	mov    rdx,QWORD PTR [rsp+0x88]
   28bfd:	add    ecx,edx
   28bff:	mov    rbx,rcx
   28c02:	shr    edx,0x3
   28c05:	xor    edx,DWORD PTR [rsp+0x68]
   28c09:	mov    rdi,QWORD PTR [rsp+0x10]
   28c0e:	mov    ecx,edi
   28c10:	rol    ecx,0xf
   28c13:	add    edx,DWORD PTR [rsp+0x78]
   28c17:	mov    rsi,rdx
   28c1a:	mov    edx,edi
   28c1c:	rol    edx,0xd
   28c1f:	xor    edx,ecx
   28c21:	mov    r9d,edi
   28c24:	shr    r9d,0xa
   28c28:	xor    r9d,edx
   28c2b:	add    esi,DWORD PTR [rsp+0x98]
   28c32:	mov    rax,QWORD PTR [rsp+0x8]
   28c37:	mov    ecx,eax
   28c39:	rol    ecx,0xf
   28c3c:	add    r9d,esi
   28c3f:	mov    edx,eax
   28c41:	rol    edx,0xd
   28c44:	xor    edx,ecx
   28c46:	mov    esi,eax
   28c48:	shr    esi,0xa
   28c4b:	xor    esi,edx
   28c4d:	add    ebx,DWORD PTR [rsp+0x18]
   28c51:	mov    ecx,r9d
   28c54:	rol    ecx,0xf
   28c57:	add    esi,ebx
   28c59:	mov    edx,r9d
   28c5c:	rol    edx,0xd
   28c5f:	xor    edx,ecx
   28c61:	mov    ebx,r9d
   28c64:	shr    ebx,0xa
   28c67:	xor    ebx,edx
   28c69:	add    r13d,DWORD PTR [rsp+0xb0]
   28c71:	mov    ecx,esi
   28c73:	rol    ecx,0xf
   28c76:	add    ebx,r13d
   28c79:	mov    edx,esi
   28c7b:	rol    edx,0xd
   28c7e:	xor    edx,ecx
   28c80:	mov    edi,esi
   28c82:	mov    QWORD PTR [rsp+0x88],rsi
   28c8a:	shr    edi,0xa
   28c8d:	xor    edi,edx
   28c8f:	add    r8d,DWORD PTR [rsp+0xa8]
   28c97:	mov    r14,QWORD PTR [rsp+0xc0]
   28c9f:	mov    ecx,r14d
   28ca2:	rol    ecx,0x1a
   28ca5:	add    edi,r8d
   28ca8:	mov    eax,r14d
   28cab:	rol    eax,0x15
   28cae:	xor    eax,ecx
   28cb0:	mov    ecx,r14d
   28cb3:	rol    ecx,0x7
   28cb6:	xor    ecx,eax
   28cb8:	mov    edx,DWORD PTR [rsp+0x28]
   28cbc:	add    edx,r9d
   28cbf:	mov    DWORD PTR [rsp+0x68],r9d
   28cc4:	mov    r13,QWORD PTR [rsp+0x20]
   28cc9:	mov    eax,r13d
   28ccc:	xor    eax,r15d
   28ccf:	and    eax,r14d
   28cd2:	xor    eax,r15d
   28cd5:	add    eax,edx
   28cd7:	add    eax,ecx
   28cd9:	add    eax,0x27b70a85
   28cde:	mov    ecx,r11d
   28ce1:	rol    ecx,0x1e
   28ce4:	mov    edx,r11d
   28ce7:	rol    edx,0x13
   28cea:	xor    edx,ecx
   28cec:	mov    ecx,r11d
   28cef:	rol    ecx,0xa
   28cf2:	xor    ecx,edx
   28cf4:	mov    r10,QWORD PTR [rsp+0x70]
   28cf9:	mov    edx,r10d
   28cfc:	xor    edx,ebp
   28cfe:	and    edx,r11d
   28d01:	mov    r8d,r10d
   28d04:	and    r8d,ebp
   28d07:	xor    r8d,edx
   28d0a:	add    r8d,ecx
   28d0d:	add    r8d,eax
   28d10:	add    r12d,eax
   28d13:	mov    eax,r12d
   28d16:	rol    eax,0x1a
   28d19:	mov    ecx,r12d
   28d1c:	rol    ecx,0x15
   28d1f:	xor    ecx,eax
   28d21:	mov    eax,r12d
   28d24:	rol    eax,0x7
   28d27:	xor    eax,ecx
   28d29:	lea    ecx,[rsi+r15*1]
   28d2d:	mov    edx,r14d
   28d30:	mov    rsi,r13
   28d33:	xor    edx,esi
   28d35:	and    edx,r12d
   28d38:	mov    r15d,r12d
   28d3b:	xor    edx,esi
   28d3d:	add    edx,ecx
   28d3f:	mov    ecx,r8d
   28d42:	rol    ecx,0x1e
   28d45:	add    eax,edx
   28d47:	add    eax,0x2e1b2138
   28d4c:	mov    edx,r8d
   28d4f:	rol    edx,0x13
   28d52:	xor    edx,ecx
   28d54:	mov    ecx,r8d
   28d57:	rol    ecx,0xa
   28d5a:	xor    ecx,edx
   28d5c:	mov    edx,r11d
   28d5f:	and    edx,r10d
   28d62:	mov    r13d,r11d
   28d65:	xor    r13d,r10d
   28d68:	and    r13d,r8d
   28d6b:	xor    r13d,edx
   28d6e:	add    r13d,ecx
   28d71:	add    ebp,eax
   28d73:	mov    ecx,ebp
   28d75:	rol    ecx,0x1a
   28d78:	add    r13d,eax
   28d7b:	mov    eax,ebp
   28d7d:	rol    eax,0x15
   28d80:	xor    eax,ecx
   28d82:	mov    ecx,ebp
   28d84:	rol    ecx,0x7
   28d87:	xor    ecx,eax
   28d89:	mov    edx,r12d
   28d8c:	xor    edx,r14d
   28d8f:	and    edx,ebp
   28d91:	xor    edx,r14d
   28d94:	add    edx,ebx
   28d96:	add    edx,esi
   28d98:	lea    eax,[rcx+rdx*1]
   28d9b:	add    eax,0x4d2c6dfc
   28da0:	mov    ecx,r13d
   28da3:	rol    ecx,0x1e
   28da6:	mov    edx,r13d
   28da9:	rol    edx,0x13
   28dac:	xor    edx,ecx
   28dae:	mov    ecx,r13d
   28db1:	rol    ecx,0xa
   28db4:	xor    ecx,edx
   28db6:	mov    edx,r8d
   28db9:	xor    edx,r11d
   28dbc:	and    edx,r13d
   28dbf:	mov    r12d,r8d
   28dc2:	and    r12d,r11d
   28dc5:	xor    r12d,edx
   28dc8:	add    r12d,ecx
   28dcb:	add    r12d,eax
   28dce:	mov    rsi,r10
   28dd1:	add    esi,eax
   28dd3:	mov    eax,esi
   28dd5:	rol    eax,0x1a
   28dd8:	mov    ecx,esi
   28dda:	rol    ecx,0x15
   28ddd:	xor    ecx,eax
   28ddf:	mov    eax,esi
   28de1:	rol    eax,0x7
   28de4:	xor    eax,ecx
   28de6:	lea    ecx,[rdi+r14*1]
   28dea:	mov    edx,ebp
   28dec:	xor    edx,r15d
   28def:	and    edx,esi
   28df1:	mov    r10,rsi
   28df4:	xor    edx,r15d
   28df7:	add    edx,ecx
   28df9:	mov    ecx,r12d
   28dfc:	rol    ecx,0x1e
   28dff:	add    eax,edx
   28e01:	add    eax,0x53380d13
   28e06:	mov    edx,r12d
   28e09:	rol    edx,0x13
   28e0c:	xor    edx,ecx
   28e0e:	mov    ecx,r12d
   28e11:	rol    ecx,0xa
   28e14:	xor    ecx,edx
   28e16:	mov    edx,r13d
   28e19:	and    edx,r8d
   28e1c:	mov    esi,r13d
   28e1f:	xor    esi,r8d
   28e22:	and    esi,r12d
   28e25:	xor    esi,edx
   28e27:	add    esi,ecx
   28e29:	add    esi,eax
   28e2b:	mov    r14,rsi
   28e2e:	mov    QWORD PTR [rsp+0x80],rbx
   28e36:	mov    ecx,ebx
   28e38:	rol    ecx,0xf
   28e3b:	add    r11d,eax
   28e3e:	mov    eax,ebx
   28e40:	rol    eax,0xd
   28e43:	xor    eax,ecx
   28e45:	mov    edx,ebx
   28e47:	shr    edx,0xa
   28e4a:	xor    edx,eax
   28e4c:	mov    rcx,QWORD PTR [rsp]
   28e50:	add    ecx,DWORD PTR [rsp+0x40]
   28e54:	mov    QWORD PTR [rsp+0x38],rdi
   28e59:	mov    eax,edi
   28e5b:	rol    eax,0xf
   28e5e:	add    edx,ecx
   28e60:	mov    ecx,edi
   28e62:	rol    ecx,0xd
   28e65:	xor    ecx,eax
   28e67:	mov    esi,edi
   28e69:	shr    esi,0xa
   28e6c:	xor    esi,ecx
   28e6e:	mov    rcx,QWORD PTR [rsp+0x58]
   28e73:	add    ecx,DWORD PTR [rsp+0x10]
   28e77:	mov    eax,edx
   28e79:	rol    eax,0xf
   28e7c:	add    esi,ecx
   28e7e:	mov    ecx,edx
   28e80:	rol    ecx,0xd
   28e83:	xor    ecx,eax
   28e85:	mov    edi,edx
   28e87:	mov    DWORD PTR [rsp+0x78],edx
   28e8b:	shr    edi,0xa
   28e8e:	xor    edi,ecx
   28e90:	mov    rcx,QWORD PTR [rsp+0x50]
   28e95:	add    ecx,DWORD PTR [rsp+0x8]
   28e99:	mov    eax,esi
   28e9b:	rol    eax,0xf
   28e9e:	add    edi,ecx
   28ea0:	mov    QWORD PTR [rsp],rdi
   28ea4:	mov    ecx,esi
   28ea6:	rol    ecx,0xd
   28ea9:	xor    ecx,eax
   28eab:	mov    eax,esi
   28ead:	mov    rbx,rsi
   28eb0:	mov    QWORD PTR [rsp+0x48],rsi
   28eb5:	shr    eax,0xa
   28eb8:	xor    eax,ecx
   28eba:	mov    rcx,rax
   28ebd:	mov    esi,DWORD PTR [rsp+0xa0]
   28ec4:	add    esi,r9d
   28ec7:	mov    eax,r11d
   28eca:	rol    eax,0x1a
   28ecd:	add    ecx,esi
   28ecf:	mov    QWORD PTR [rsp+0x20],rcx
   28ed4:	mov    ecx,r11d
   28ed7:	rol    ecx,0x15
   28eda:	xor    ecx,eax
   28edc:	mov    eax,r11d
   28edf:	rol    eax,0x7
   28ee2:	xor    eax,ecx
   28ee4:	add    r15d,edx
   28ee7:	mov    ecx,r10d
   28eea:	xor    ecx,ebp
   28eec:	and    ecx,r11d
   28eef:	xor    ecx,ebp
   28ef1:	add    ecx,r15d
   28ef4:	add    ecx,eax
   28ef6:	add    ecx,0x650a7354
   28efc:	mov    r15,r14
   28eff:	mov    eax,r15d
   28f02:	rol    eax,0x1e
   28f05:	mov    edx,r15d
   28f08:	rol    edx,0x13
   28f0b:	xor    edx,eax
   28f0d:	mov    r9d,r15d
   28f10:	rol    r9d,0xa
   28f14:	xor    r9d,edx
   28f17:	mov    edx,r12d
   28f1a:	xor    edx,r13d
   28f1d:	and    edx,r15d
   28f20:	mov    eax,r12d
   28f23:	and    eax,r13d
   28f26:	xor    eax,edx
   28f28:	add    eax,r9d
   28f2b:	add    eax,ecx
   28f2d:	mov    esi,r8d
   28f30:	add    esi,ecx
   28f32:	mov    ecx,esi
   28f34:	rol    ecx,0x1a
   28f37:	mov    edx,esi
   28f39:	rol    edx,0x15
   28f3c:	xor    edx,ecx
   28f3e:	mov    ecx,esi
   28f40:	rol    ecx,0x7
   28f43:	xor    ecx,edx
   28f45:	lea    edx,[rbx+rbp*1]
   28f48:	mov    r9d,r11d
   28f4b:	xor    r9d,r10d
   28f4e:	and    r9d,esi
   28f51:	xor    r9d,r10d
   28f54:	mov    r8,r10
   28f57:	add    r9d,edx
   28f5a:	mov    edx,eax
   28f5c:	rol    edx,0x1e
   28f5f:	add    ecx,r9d
   28f62:	add    ecx,0x766a0abb
   28f68:	mov    r9d,eax
   28f6b:	rol    r9d,0x13
   28f6f:	xor    r9d,edx
   28f72:	mov    edx,eax
   28f74:	mov    ebp,eax
   28f76:	rol    edx,0xa
   28f79:	xor    edx,r9d
   28f7c:	mov    r10d,r15d
   28f7f:	and    r10d,r12d
   28f82:	mov    eax,r15d
   28f85:	xor    eax,r12d
   28f88:	and    eax,ebp
   28f8a:	xor    eax,r10d
   28f8d:	add    eax,edx
   28f8f:	mov    rbx,rax
   28f92:	add    r13d,ecx
   28f95:	mov    edx,r13d
   28f98:	rol    edx,0x1a
   28f9b:	add    ebx,ecx
   28f9d:	mov    ecx,r13d
   28fa0:	rol    ecx,0x15
   28fa3:	xor    ecx,edx
   28fa5:	mov    edx,r13d
   28fa8:	rol    edx,0x7
   28fab:	xor    edx,ecx
   28fad:	mov    r10d,esi
   28fb0:	xor    r10d,r11d
   28fb3:	and    r10d,r13d
   28fb6:	xor    r10d,r11d
   28fb9:	add    r10d,edi
   28fbc:	add    r10d,r8d
   28fbf:	lea    ecx,[rdx+r10*1]
   28fc3:	add    ecx,0x81c2c92e
   28fc9:	mov    edx,ebx
   28fcb:	rol    edx,0x1e
   28fce:	mov    r10d,ebx
   28fd1:	rol    r10d,0x13
   28fd5:	xor    r10d,edx
   28fd8:	mov    edx,ebx
   28fda:	rol    edx,0xa
   28fdd:	xor    edx,r10d
   28fe0:	mov    r10d,ebp
   28fe3:	mov    QWORD PTR [rsp+0x70],r14
   28fe8:	xor    r10d,r15d
   28feb:	and    r10d,ebx
   28fee:	mov    eax,ebp
   28ff0:	and    eax,r15d
   28ff3:	xor    eax,r10d
   28ff6:	add    eax,edx
   28ff8:	add    eax,ecx
   28ffa:	mov    rdi,rax
   28ffd:	add    r12d,ecx
   29000:	mov    ecx,r12d
   29003:	rol    ecx,0x1a
   29006:	mov    edx,r12d
   29009:	rol    edx,0x15
   2900c:	xor    edx,ecx
   2900e:	mov    ecx,r12d
   29011:	mov    QWORD PTR [rsp+0x50],r12
   29016:	rol    ecx,0x7
   29019:	xor    ecx,edx
   2901b:	mov    rax,QWORD PTR [rsp+0x20]
   29020:	lea    edx,[rax+r11*1]
   29024:	mov    r8d,r13d
   29027:	mov    DWORD PTR [rsp+0xc0],esi
   2902e:	xor    r8d,esi
   29031:	and    r8d,r12d
   29034:	xor    r8d,esi
   29037:	add    r8d,edx
   2903a:	mov    edx,edi
   2903c:	rol    edx,0x1e
   2903f:	lea    r9d,[rcx+r8*1]
   29043:	add    r9d,0x92722c85
   2904a:	mov    ecx,edi
   2904c:	rol    ecx,0x13
   2904f:	xor    ecx,edx
   29051:	mov    r14d,edi
   29054:	mov    QWORD PTR [rsp+0xc8],rdi
   2905c:	rol    r14d,0xa
   29060:	xor    r14d,ecx
   29063:	mov    esi,DWORD PTR [rsp+0xa8]
   2906a:	mov    r10d,esi
   2906d:	rol    r10d,0x19
   29071:	mov    rdx,QWORD PTR [rsp+0xb0]
   29079:	mov    eax,edx
   2907b:	rol    eax,0x19
   2907e:	mov    DWORD PTR [rsp+0x28],eax
   29082:	mov    r15,rbx
   29085:	mov    QWORD PTR [rsp+0xb8],rbx
   2908d:	mov    r11d,r15d
   29090:	mov    DWORD PTR [rsp+0xa0],ebp
   29097:	and    r11d,ebp
   2909a:	mov    rcx,QWORD PTR [rsp+0x18]
   2909f:	mov    r12d,ecx
   290a2:	rol    r12d,0x19
   290a6:	mov    rax,QWORD PTR [rsp+0x98]
   290ae:	mov    r8d,eax
   290b1:	rol    r8d,0x19
   290b5:	mov    DWORD PTR [rsp+0x60],r8d
   290ba:	xor    r15d,ebp
   290bd:	mov    r8d,esi
   290c0:	rol    r8d,0xe
   290c4:	mov    ebx,r8d
   290c7:	and    r15d,edi
   290ca:	mov    esi,edx
   290cc:	rol    esi,0xe
   290cf:	xor    r15d,r11d
   290d2:	mov    r8d,ecx
   290d5:	rol    r8d,0xe
   290d9:	add    r15d,r14d
   290dc:	rol    eax,0xe
   290df:	mov    DWORD PTR [rsp+0x58],eax
   290e3:	add    r15d,r9d
   290e6:	mov    QWORD PTR [rsp+0xf0],r15
   290ee:	mov    eax,DWORD PTR [rsp+0x68]
   290f2:	mov    ecx,eax
   290f4:	rol    ecx,0x19
   290f7:	mov    rdi,QWORD PTR [rsp+0x70]
   290fc:	add    edi,r9d
   290ff:	mov    QWORD PTR [rsp+0x70],rdi
   29104:	mov    r9,QWORD PTR [rsp+0x8]
   29109:	mov    edx,r9d
   2910c:	rol    edx,0x19
   2910f:	mov    r11d,ebx
   29112:	xor    r11d,r10d
   29115:	mov    rbp,QWORD PTR [rsp+0x10]
   2911a:	mov    r10d,ebp
   2911d:	rol    r10d,0x19
   29121:	mov    ebx,esi
   29123:	xor    ebx,DWORD PTR [rsp+0x28]
   29127:	mov    rdi,QWORD PTR [rsp+0x40]
   2912c:	mov    esi,edi
   2912e:	rol    esi,0x19
   29131:	mov    r14d,r8d
   29134:	xor    r14d,r12d
   29137:	mov    r12d,eax
   2913a:	mov    r8d,eax
   2913d:	rol    r12d,0xe
   29141:	mov    r15d,DWORD PTR [rsp+0x58]
   29146:	xor    r15d,DWORD PTR [rsp+0x60]
   2914b:	mov    eax,r9d
   2914e:	rol    eax,0xe
   29151:	xor    r12d,ecx
   29154:	mov    ecx,ebp
   29156:	rol    ecx,0xe
   29159:	xor    eax,edx
   2915b:	mov    edx,edi
   2915d:	rol    edx,0xe
   29160:	xor    ecx,r10d
   29163:	xor    edx,esi
   29165:	mov    esi,r8d
   29168:	shr    esi,0x3
   2916b:	xor    esi,r12d
   2916e:	add    esi,r9d
   29171:	shr    r9d,0x3
   29175:	xor    r9d,eax
   29178:	mov    rax,rbp
   2917b:	add    r9d,eax
   2917e:	mov    QWORD PTR [rsp+0x8],r9
   29183:	shr    eax,0x3
   29186:	xor    eax,ecx
   29188:	add    eax,edi
   2918a:	mov    QWORD PTR [rsp+0x10],rax
   2918f:	shr    edi,0x3
   29192:	xor    edi,edx
   29194:	mov    r10d,DWORD PTR [rsp+0xa8]
   2919c:	add    edi,r10d
   2919f:	mov    QWORD PTR [rsp+0x40],rdi
   291a4:	shr    r10d,0x3
   291a8:	xor    r10d,r11d
   291ab:	mov    r12,QWORD PTR [rsp+0xb0]
   291b3:	add    r10d,r12d
   291b6:	shr    r12d,0x3
   291ba:	xor    r12d,ebx
   291bd:	mov    rax,QWORD PTR [rsp+0x18]
   291c2:	add    r12d,eax
   291c5:	shr    eax,0x3
   291c8:	xor    eax,r14d
   291cb:	mov    rcx,QWORD PTR [rsp+0x98]
   291d3:	add    eax,ecx
   291d5:	mov    r11,rax
   291d8:	shr    ecx,0x3
   291db:	xor    ecx,r15d
   291de:	add    ecx,DWORD PTR [rsp+0x34]
   291e2:	mov    r8,rcx
   291e5:	mov    rdx,QWORD PTR [rsp]
   291e9:	mov    eax,edx
   291eb:	rol    eax,0xf
   291ee:	mov    ecx,edx
   291f0:	rol    ecx,0xd
   291f3:	xor    ecx,eax
   291f5:	shr    edx,0xa
   291f8:	xor    edx,ecx
   291fa:	add    r8d,DWORD PTR [rsp+0x88]
   29202:	add    edx,r8d
   29205:	mov    r8,QWORD PTR [rsp+0x20]
   2920a:	mov    eax,r8d
   2920d:	rol    eax,0xf
   29210:	mov    ecx,r8d
   29213:	rol    ecx,0xd
   29216:	xor    ecx,eax
   29218:	shr    r8d,0xa
   2921c:	xor    r8d,ecx
   2921f:	add    r11d,DWORD PTR [rsp+0x80]
   29227:	add    r8d,r11d
   2922a:	mov    eax,edx
   2922c:	rol    eax,0xf
   2922f:	mov    ecx,edx
   29231:	rol    ecx,0xd
   29234:	xor    ecx,eax
   29236:	mov    eax,edx
   29238:	mov    DWORD PTR [rsp+0x58],edx
   2923c:	shr    eax,0xa
   2923f:	xor    eax,ecx
   29241:	add    r12d,DWORD PTR [rsp+0x38]
   29246:	add    eax,r12d
   29249:	mov    r14,rax
   2924c:	mov    eax,r8d
   2924f:	rol    eax,0xf
   29252:	mov    ecx,r8d
   29255:	rol    ecx,0xd
   29258:	xor    ecx,eax
   2925a:	mov    eax,r8d
   2925d:	mov    r11,r8
   29260:	mov    QWORD PTR [rsp+0x60],r8
   29265:	shr    eax,0xa
   29268:	xor    eax,ecx
   2926a:	add    r10d,DWORD PTR [rsp+0x78]
   2926f:	add    eax,r10d
   29272:	mov    r8,rax
   29275:	mov    rbp,QWORD PTR [rsp+0x70]
   2927a:	mov    eax,ebp
   2927c:	rol    eax,0x1a
   2927f:	mov    ecx,ebp
   29281:	rol    ecx,0x15
   29284:	xor    ecx,eax
   29286:	mov    eax,ebp
   29288:	rol    eax,0x7
   2928b:	xor    eax,ecx
   2928d:	mov    edi,DWORD PTR [rsp+0xc0]
   29294:	add    edi,edx
   29296:	mov    r10,QWORD PTR [rsp+0x50]
   2929b:	mov    ecx,r10d
   2929e:	xor    ecx,r13d
   292a1:	and    ecx,ebp
   292a3:	xor    ecx,r13d
   292a6:	add    ecx,edi
   292a8:	mov    r15,QWORD PTR [rsp+0xf0]
   292b0:	mov    edx,r15d
   292b3:	rol    edx,0x1e
   292b6:	add    eax,ecx
   292b8:	add    eax,0xa2bfe8a1
   292bd:	mov    ecx,r15d
   292c0:	rol    ecx,0x13
   292c3:	xor    ecx,edx
   292c5:	mov    edx,r15d
   292c8:	rol    edx,0xa
   292cb:	xor    edx,ecx
   292cd:	mov    r12,QWORD PTR [rsp+0xc8]
   292d5:	mov    ecx,r12d
   292d8:	mov    rbx,QWORD PTR [rsp+0xb8]
   292e0:	xor    ecx,ebx
   292e2:	and    ecx,r15d
   292e5:	mov    edi,r12d
   292e8:	and    edi,ebx
   292ea:	xor    edi,ecx
   292ec:	add    edi,edx
   292ee:	mov    r9d,DWORD PTR [rsp+0xa0]
   292f6:	add    r9d,eax
   292f9:	mov    ecx,r9d
   292fc:	rol    ecx,0x1a
   292ff:	add    edi,eax
   29301:	mov    eax,r9d
   29304:	rol    eax,0x15
   29307:	xor    eax,ecx
   29309:	mov    ecx,r9d
   2930c:	rol    ecx,0x7
   2930f:	xor    ecx,eax
   29311:	mov    edx,ebp
   29313:	xor    edx,r10d
   29316:	and    edx,r9d
   29319:	xor    edx,r10d
   2931c:	add    edx,r11d
   2931f:	add    edx,r13d
   29322:	lea    eax,[rcx+rdx*1]
   29325:	add    eax,0xa81a664b
   2932a:	mov    ecx,edi
   2932c:	rol    ecx,0x1e
   2932f:	mov    edx,edi
   29331:	rol    edx,0x13
   29334:	xor    edx,ecx
   29336:	mov    ecx,edi
   29338:	rol    ecx,0xa
   2933b:	xor    ecx,edx
   2933d:	mov    edx,r15d
   29340:	and    edx,r12d
   29343:	mov    r11d,r15d
   29346:	xor    r11d,r12d
   29349:	and    r11d,edi
   2934c:	xor    r11d,edx
   2934f:	add    r11d,ecx
   29352:	add    r11d,eax
   29355:	add    ebx,eax
   29357:	mov    eax,ebx
   29359:	rol    eax,0x1a
   2935c:	mov    ecx,ebx
   2935e:	rol    ecx,0x15
   29361:	xor    ecx,eax
   29363:	mov    eax,ebx
   29365:	rol    eax,0x7
   29368:	xor    eax,ecx
   2936a:	mov    edx,r9d
   2936d:	xor    edx,ebp
   2936f:	and    edx,ebx
   29371:	xor    edx,ebp
   29373:	add    edx,r14d
   29376:	add    edx,r10d
   29379:	mov    ecx,r11d
   2937c:	rol    ecx,0x1e
   2937f:	add    eax,edx
   29381:	add    eax,0xc24b8b70
   29386:	mov    edx,r11d
   29389:	rol    edx,0x13
   2938c:	xor    edx,ecx
   2938e:	mov    ecx,r11d
   29391:	rol    ecx,0xa
   29394:	xor    ecx,edx
   29396:	mov    edx,edi
   29398:	xor    edx,r15d
   2939b:	and    edx,r11d
   2939e:	mov    r10d,edi
   293a1:	and    r10d,r15d
   293a4:	xor    r10d,edx
   293a7:	add    r10d,ecx
   293aa:	mov    r13,r12
   293ad:	add    r13d,eax
   293b0:	mov    ecx,r13d
   293b3:	rol    ecx,0x1a
   293b6:	add    r10d,eax
   293b9:	mov    r12,r10
   293bc:	mov    eax,r13d
   293bf:	rol    eax,0x15
   293c2:	xor    eax,ecx
   293c4:	mov    ecx,r13d
   293c7:	rol    ecx,0x7
   293ca:	xor    ecx,eax
   293cc:	mov    edx,ebx
   293ce:	xor    edx,r9d
   293d1:	and    edx,r13d
   293d4:	xor    edx,r9d
   293d7:	add    edx,r8d
   293da:	add    edx,ebp
   293dc:	lea    eax,[rcx+rdx*1]
   293df:	add    eax,0xc76c51a3
   293e4:	mov    ecx,r12d
   293e7:	rol    ecx,0x1e
   293ea:	mov    edx,r12d
   293ed:	rol    edx,0x13
   293f0:	xor    edx,ecx
   293f2:	mov    ecx,r12d
   293f5:	rol    ecx,0xa
   293f8:	xor    ecx,edx
   293fa:	mov    edx,r11d
   293fd:	and    edx,edi
   293ff:	mov    r10d,r11d
   29402:	xor    r10d,edi
   29405:	and    r10d,r12d
   29408:	xor    r10d,edx
   2940b:	add    r10d,ecx
   2940e:	add    r10d,eax
   29411:	add    r15d,eax
   29414:	mov    QWORD PTR [rsp+0x28],r14
   29419:	mov    eax,r14d
   2941c:	rol    eax,0xf
   2941f:	mov    ecx,r14d
   29422:	rol    ecx,0xd
   29425:	xor    ecx,eax
   29427:	mov    edx,r14d
   2942a:	shr    edx,0xa
   2942d:	xor    edx,ecx
   2942f:	mov    rax,QWORD PTR [rsp+0x40]
   29434:	add    eax,DWORD PTR [rsp+0x48]
   29438:	add    edx,eax
   2943a:	mov    QWORD PTR [rsp+0x18],r8
   2943f:	mov    eax,r8d
   29442:	rol    eax,0xf
   29445:	mov    ecx,r8d
   29448:	rol    ecx,0xd
   2944b:	xor    ecx,eax
   2944d:	mov    r14d,r8d
   29450:	shr    r14d,0xa
   29454:	xor    r14d,ecx
   29457:	mov    rax,QWORD PTR [rsp+0x10]
   2945c:	add    eax,DWORD PTR [rsp]
   2945f:	add    r14d,eax
   29462:	mov    eax,edx
   29464:	rol    eax,0xf
   29467:	mov    ecx,edx
   29469:	rol    ecx,0xd
   2946c:	xor    ecx,eax
   2946e:	mov    eax,edx
   29470:	mov    DWORD PTR [rsp+0xb0],edx
   29477:	shr    eax,0xa
   2947a:	xor    eax,ecx
   2947c:	mov    rcx,QWORD PTR [rsp+0x8]
   29481:	add    ecx,DWORD PTR [rsp+0x20]
   29485:	add    eax,ecx
   29487:	mov    rbp,rax
   2948a:	mov    QWORD PTR [rsp+0xa8],rax
   29492:	mov    eax,r14d
   29495:	rol    eax,0xf
   29498:	mov    ecx,r14d
   2949b:	rol    ecx,0xd
   2949e:	xor    ecx,eax
   294a0:	mov    eax,r14d
   294a3:	mov    QWORD PTR [rsp+0x10],r14
   294a8:	shr    eax,0xa
   294ab:	xor    eax,ecx
   294ad:	add    esi,DWORD PTR [rsp+0x58]
   294b1:	add    eax,esi
   294b3:	mov    QWORD PTR [rsp+0x40],rax
   294b8:	mov    eax,r15d
   294bb:	rol    eax,0x1a
   294be:	mov    ecx,r15d
   294c1:	rol    ecx,0x15
   294c4:	xor    ecx,eax
   294c6:	mov    eax,r15d
   294c9:	rol    eax,0x7
   294cc:	xor    eax,ecx
   294ce:	add    r9d,edx
   294d1:	mov    ecx,r13d
   294d4:	xor    ecx,ebx
   294d6:	and    ecx,r15d
   294d9:	xor    ecx,ebx
   294db:	add    ecx,r9d
   294de:	mov    edx,r10d
   294e1:	rol    edx,0x1e
   294e4:	add    eax,ecx
   294e6:	add    eax,0xd192e819
   294eb:	mov    ecx,r10d
   294ee:	rol    ecx,0x13
   294f1:	xor    ecx,edx
   294f3:	mov    edx,r10d
   294f6:	rol    edx,0xa
   294f9:	xor    edx,ecx
   294fb:	mov    ecx,r12d
   294fe:	xor    ecx,r11d
   29501:	and    ecx,r10d
   29504:	mov    esi,r12d
   29507:	and    esi,r11d
   2950a:	xor    esi,ecx
   2950c:	add    esi,edx
   2950e:	add    edi,eax
   29510:	mov    ecx,edi
   29512:	rol    ecx,0x1a
   29515:	add    esi,eax
   29517:	mov    eax,edi
   29519:	rol    eax,0x15
   2951c:	xor    eax,ecx
   2951e:	mov    ecx,edi
   29520:	mov    r9d,edi
   29523:	rol    ecx,0x7
   29526:	xor    ecx,eax
   29528:	mov    edx,r15d
   2952b:	xor    edx,r13d
   2952e:	and    edx,edi
   29530:	xor    edx,r13d
   29533:	add    edx,r14d
   29536:	add    edx,ebx
   29538:	lea    eax,[rcx+rdx*1]
   2953b:	add    eax,0xd6990624
   29540:	mov    ecx,esi
   29542:	rol    ecx,0x1e
   29545:	mov    edx,esi
   29547:	rol    edx,0x13
   2954a:	xor    edx,ecx
   2954c:	mov    ecx,esi
   2954e:	rol    ecx,0xa
   29551:	xor    ecx,edx
   29553:	mov    edx,r10d
   29556:	and    edx,r12d
   29559:	mov    r8d,r10d
   2955c:	xor    r8d,r12d
   2955f:	and    r8d,esi
   29562:	mov    edi,esi
   29564:	xor    r8d,edx
   29567:	add    r8d,ecx
   2956a:	add    r8d,eax
   2956d:	add    r11d,eax
   29570:	mov    eax,r11d
   29573:	rol    eax,0x1a
   29576:	mov    ecx,r11d
   29579:	rol    ecx,0x15
   2957c:	xor    ecx,eax
   2957e:	mov    eax,r11d
   29581:	rol    eax,0x7
   29584:	xor    eax,ecx
   29586:	mov    edx,r9d
   29589:	xor    edx,r15d
   2958c:	and    edx,r11d
   2958f:	xor    edx,r15d
   29592:	add    edx,ebp
   29594:	add    edx,r13d
   29597:	mov    ecx,r8d
   2959a:	rol    ecx,0x1e
   2959d:	add    eax,edx
   2959f:	add    eax,0xf40e3585
   295a4:	mov    edx,r8d
   295a7:	rol    edx,0x13
   295aa:	xor    edx,ecx
   295ac:	mov    ecx,r8d
   295af:	rol    ecx,0xa
   295b2:	xor    ecx,edx
   295b4:	mov    edx,esi
   295b6:	xor    edx,r10d
   295b9:	and    edx,r8d
   295bc:	and    esi,r10d
   295bf:	xor    esi,edx
   295c1:	add    esi,ecx
   295c3:	add    r12d,eax
   295c6:	mov    ecx,r12d
   295c9:	rol    ecx,0x1a
   295cc:	add    esi,eax
   295ce:	mov    eax,r12d
   295d1:	rol    eax,0x15
   295d4:	xor    eax,ecx
   295d6:	mov    ecx,r12d
   295d9:	mov    QWORD PTR [rsp+0x70],r12
   295de:	rol    ecx,0x7
   295e1:	xor    ecx,eax
   295e3:	mov    rax,QWORD PTR [rsp+0x40]
   295e8:	add    eax,r15d
   295eb:	mov    edx,r11d
   295ee:	mov    DWORD PTR [rsp+0x8],r9d
   295f3:	xor    edx,r9d
   295f6:	and    edx,r12d
   295f9:	xor    edx,r9d
   295fc:	add    edx,eax
   295fe:	lea    ebx,[rcx+rdx*1]
   29601:	add    ebx,0x106aa070
   29607:	mov    eax,esi
   29609:	rol    eax,0x1e
   2960c:	mov    ecx,esi
   2960e:	rol    ecx,0x13
   29611:	xor    ecx,eax
   29613:	mov    edx,esi
   29615:	mov    QWORD PTR [rsp+0xc0],rsi
   2961d:	rol    edx,0xa
   29620:	xor    edx,ecx
   29622:	mov    r15,r8
   29625:	mov    QWORD PTR [rsp+0xc8],r8
   2962d:	mov    eax,r15d
   29630:	mov    DWORD PTR [rsp+0x34],edi
   29634:	and    eax,edi
   29636:	mov    r8d,DWORD PTR [rsp+0x78]
   2963b:	mov    r9d,r8d
   2963e:	rol    r9d,0x19
   29642:	mov    r12,QWORD PTR [rsp+0x38]
   29647:	mov    r13d,r12d
   2964a:	rol    r13d,0x19
   2964e:	xor    r15d,edi
   29651:	mov    rdi,QWORD PTR [rsp+0x80]
   29659:	mov    r14d,edi
   2965c:	rol    r14d,0x19
   29660:	and    r15d,esi
   29663:	mov    rsi,QWORD PTR [rsp+0x88]
   2966b:	mov    ecx,esi
   2966d:	rol    ecx,0x19
   29670:	xor    r15d,eax
   29673:	mov    eax,r8d
   29676:	rol    eax,0xe
   29679:	add    r15d,edx
   2967c:	rol    r12d,0xe
   29680:	add    r15d,ebx
   29683:	mov    QWORD PTR [rsp+0xa0],r15
   2968b:	mov    ebp,edi
   2968d:	rol    ebp,0xe
   29690:	add    r10d,ebx
   29693:	mov    ebx,esi
   29695:	rol    ebx,0xe
   29698:	xor    eax,r9d
   2969b:	mov    edi,eax
   2969d:	mov    esi,DWORD PTR [rsp+0x58]
   296a1:	mov    r9d,esi
   296a4:	rol    r9d,0x19
   296a8:	xor    r12d,r13d
   296ab:	mov    rdx,QWORD PTR [rsp+0x20]
   296b0:	mov    r15d,edx
   296b3:	rol    r15d,0x19
   296b7:	xor    ebp,r14d
   296ba:	mov    r8,QWORD PTR [rsp]
   296be:	mov    r14d,r8d
   296c1:	rol    r14d,0x19
   296c5:	xor    ebx,ecx
   296c7:	mov    ecx,esi
   296c9:	rol    ecx,0xe
   296cc:	xor    ecx,r9d
   296cf:	mov    r9d,edx
   296d2:	rol    r9d,0xe
   296d6:	xor    r9d,r15d
   296d9:	mov    r15d,r8d
   296dc:	rol    r15d,0xe
   296e0:	xor    r15d,r14d
   296e3:	mov    rax,QWORD PTR [rsp+0x48]
   296e8:	mov    r14d,eax
   296eb:	rol    r14d,0x19
   296ef:	mov    r13d,eax
   296f2:	rol    r13d,0xe
   296f6:	xor    r13d,r14d
   296f9:	mov    r14d,esi
   296fc:	shr    r14d,0x3
   29700:	xor    r14d,ecx
   29703:	add    r14d,edx
   29706:	mov    DWORD PTR [rsp+0x98],r14d
   2970e:	shr    edx,0x3
   29711:	xor    edx,r9d
   29714:	mov    rcx,r8
   29717:	add    edx,ecx
   29719:	mov    QWORD PTR [rsp+0x20],rdx
   2971e:	shr    ecx,0x3
   29721:	xor    ecx,r15d
   29724:	add    ecx,eax
   29726:	mov    QWORD PTR [rsp],rcx
   2972a:	shr    eax,0x3
   2972d:	xor    eax,r13d
   29730:	mov    ecx,DWORD PTR [rsp+0x78]
   29734:	add    eax,ecx
   29736:	mov    QWORD PTR [rsp+0x48],rax
   2973b:	shr    ecx,0x3
   2973e:	xor    ecx,edi
   29740:	mov    r9,QWORD PTR [rsp+0x38]
   29745:	add    ecx,r9d
   29748:	shr    r9d,0x3
   2974c:	xor    r9d,r12d
   2974f:	mov    rax,QWORD PTR [rsp+0x80]
   29757:	add    r9d,eax
   2975a:	shr    eax,0x3
   2975d:	xor    eax,ebp
   2975f:	mov    rdx,QWORD PTR [rsp+0x88]
   29767:	add    eax,edx
   29769:	mov    r14,rax
   2976c:	shr    edx,0x3
   2976f:	xor    edx,ebx
   29771:	mov    rdi,QWORD PTR [rsp+0xa8]
   29779:	mov    eax,edi
   2977b:	rol    eax,0xf
   2977e:	add    edx,DWORD PTR [rsp+0x68]
   29782:	mov    rbx,rdx
   29785:	mov    edx,edi
   29787:	rol    edx,0xd
   2978a:	xor    edx,eax
   2978c:	shr    edi,0xa
   2978f:	xor    edi,edx
   29791:	mov    r12,QWORD PTR [rsp+0x60]
   29796:	add    ebx,r12d
   29799:	mov    r15,QWORD PTR [rsp+0x40]
   2979e:	mov    eax,r15d
   297a1:	rol    eax,0xf
   297a4:	add    edi,ebx
   297a6:	mov    edx,r15d
   297a9:	rol    edx,0xd
   297ac:	xor    edx,eax
   297ae:	shr    r15d,0xa
   297b2:	xor    r15d,edx
   297b5:	mov    rbp,QWORD PTR [rsp+0x28]
   297ba:	add    r14d,ebp
   297bd:	mov    eax,edi
   297bf:	rol    eax,0xf
   297c2:	add    r15d,r14d
   297c5:	mov    edx,edi
   297c7:	rol    edx,0xd
   297ca:	xor    edx,eax
   297cc:	mov    ebx,r15d
   297cf:	rol    ebx,0xf
   297d2:	mov    eax,r15d
   297d5:	rol    eax,0xd
   297d8:	mov    esi,edi
   297da:	shr    esi,0xa
   297dd:	mov    r14d,r10d
   297e0:	rol    r14d,0x1a
   297e4:	xor    esi,edx
   297e6:	mov    edx,r10d
   297e9:	rol    edx,0x15
   297ec:	mov    r8,QWORD PTR [rsp+0x18]
   297f1:	add    r9d,r8d
   297f4:	mov    r13d,r10d
   297f7:	rol    r13d,0x7
   297fb:	mov    QWORD PTR [rsp+0x50],r13
   29800:	add    esi,r9d
   29803:	mov    QWORD PTR [rsp+0x88],rsi
   2980b:	mov    r13d,DWORD PTR [rsp+0xb0]
   29813:	mov    esi,r13d
   29816:	rol    esi,0x19
   29819:	mov    DWORD PTR [rsp+0x68],esi
   2981d:	xor    eax,ebx
   2981f:	mov    rbx,r8
   29822:	mov    esi,ebx
   29824:	rol    esi,0x19
   29827:	mov    DWORD PTR [rsp+0x78],esi
   2982b:	mov    rsi,rbp
   2982e:	mov    r8d,ebp
   29831:	rol    r8d,0x19
   29835:	mov    DWORD PTR [rsp+0x38],r8d
   2983a:	mov    r8d,r15d
   2983d:	shr    r8d,0xa
   29841:	mov    r9,r12
   29844:	mov    ebp,r9d
   29847:	rol    ebp,0x19
   2984a:	mov    DWORD PTR [rsp+0xb8],ebp
   29851:	xor    r8d,eax
   29854:	mov    eax,r13d
   29857:	rol    eax,0xe
   2985a:	mov    ebp,eax
   2985c:	add    ecx,r13d
   2985f:	mov    eax,ebx
   29861:	rol    eax,0xe
   29864:	mov    ebx,eax
   29866:	add    r8d,ecx
   29869:	mov    QWORD PTR [rsp+0x80],r8
   29871:	mov    eax,esi
   29873:	rol    eax,0xe
   29876:	mov    ecx,eax
   29878:	xor    edx,r14d
   2987b:	mov    esi,r9d
   2987e:	rol    esi,0xe
   29881:	mov    rax,QWORD PTR [rsp+0x50]
   29886:	xor    eax,edx
   29888:	mov    QWORD PTR [rsp+0x50],rax
   2988d:	mov    eax,edi
   2988f:	rol    eax,0x19
   29892:	xor    ebp,DWORD PTR [rsp+0x68]
   29896:	mov    DWORD PTR [rsp+0x68],ebp
   2989a:	mov    r12,QWORD PTR [rsp+0x40]
   2989f:	mov    r14d,r12d
   298a2:	rol    r14d,0x19
   298a6:	xor    ebx,DWORD PTR [rsp+0x78]
   298aa:	mov    DWORD PTR [rsp+0x78],ebx
   298ae:	mov    r8,QWORD PTR [rsp+0xa8]
   298b6:	mov    r9d,r8d
   298b9:	rol    r9d,0x19
   298bd:	xor    ecx,DWORD PTR [rsp+0x38]
   298c1:	mov    DWORD PTR [rsp+0x38],ecx
   298c5:	mov    rcx,QWORD PTR [rsp+0x10]
   298ca:	mov    ebx,ecx
   298cc:	rol    ebx,0x19
   298cf:	xor    esi,DWORD PTR [rsp+0xb8]
   298d6:	mov    r13d,edi
   298d9:	rol    r13d,0xe
   298dd:	xor    r13d,eax
   298e0:	mov    edx,r12d
   298e3:	rol    edx,0xe
   298e6:	xor    edx,r14d
   298e9:	mov    eax,r8d
   298ec:	rol    eax,0xe
   298ef:	xor    eax,r9d
   298f2:	mov    r14d,ecx
   298f5:	rol    r14d,0xe
   298f9:	xor    r14d,ebx
   298fc:	mov    ebp,DWORD PTR [rsp+0x8]
   29900:	add    ebp,edi
   29902:	add    DWORD PTR [rsp+0x98],edi
   29909:	shr    edi,0x3
   2990c:	xor    edi,r13d
   2990f:	mov    r9,rdi
   29912:	mov    rdi,QWORD PTR [rsp+0x20]
   29917:	add    edi,r12d
   2991a:	mov    QWORD PTR [rsp+0x20],rdi
   2991f:	mov    rdi,r12
   29922:	add    r9d,edi
   29925:	mov    QWORD PTR [rsp+0x8],r9
   2992a:	shr    edi,0x3
   2992d:	xor    edi,edx
   2992f:	mov    r13,QWORD PTR [rsp]
   29933:	mov    rdx,r8
   29936:	add    r13d,edx
   29939:	add    edi,edx
   2993b:	mov    QWORD PTR [rsp],rdi
   2993f:	shr    edx,0x3
   29942:	xor    edx,eax
   29944:	mov    rax,rcx
   29947:	mov    r12,QWORD PTR [rsp+0x48]
   2994c:	add    r12d,eax
   2994f:	add    edx,eax
   29951:	mov    DWORD PTR [rsp+0x40],edx
   29955:	shr    eax,0x3
   29958:	xor    eax,r14d
   2995b:	mov    ecx,DWORD PTR [rsp+0xb0]
   29962:	add    eax,ecx
   29964:	mov    QWORD PTR [rsp+0x10],rax
   29969:	shr    ecx,0x3
   2996c:	xor    ecx,DWORD PTR [rsp+0x68]
   29970:	mov    rax,QWORD PTR [rsp+0x18]
   29975:	add    ecx,eax
   29977:	mov    DWORD PTR [rsp+0x48],ecx
   2997b:	shr    eax,0x3
   2997e:	xor    eax,DWORD PTR [rsp+0x78]
   29982:	mov    rcx,QWORD PTR [rsp+0x28]
   29987:	add    eax,ecx
   29989:	mov    QWORD PTR [rsp+0x18],rax
   2998e:	shr    ecx,0x3
   29991:	xor    ecx,DWORD PTR [rsp+0x38]
   29995:	mov    rax,QWORD PTR [rsp+0x60]
   2999a:	add    ecx,eax
   2999c:	mov    QWORD PTR [rsp+0x28],rcx
   299a1:	shr    eax,0x3
   299a4:	xor    eax,esi
   299a6:	add    eax,DWORD PTR [rsp+0x58]
   299aa:	add    eax,r15d
   299ad:	mov    QWORD PTR [rsp+0x60],rax
   299b2:	lea    eax,[r15+r11*1]
   299b6:	mov    rdx,QWORD PTR [rsp+0x70]
   299bb:	mov    r9d,edx
   299be:	xor    r9d,r11d
   299c1:	and    r9d,r10d
   299c4:	xor    r9d,r11d
   299c7:	add    r9d,ebp
   299ca:	mov    rcx,QWORD PTR [rsp+0x50]
   299cf:	add    r9d,ecx
   299d2:	add    r9d,0x19a4c116
   299d9:	mov    rsi,QWORD PTR [rsp+0xa0]
   299e1:	mov    r11d,esi
   299e4:	rol    r11d,0x1e
   299e8:	mov    ebp,esi
   299ea:	rol    ebp,0x13
   299ed:	xor    ebp,r11d
   299f0:	mov    r11d,esi
   299f3:	rol    r11d,0xa
   299f7:	xor    r11d,ebp
   299fa:	mov    r15,QWORD PTR [rsp+0xc0]
   29a02:	mov    r14d,r15d
   29a05:	mov    rbx,QWORD PTR [rsp+0xc8]
   29a0d:	xor    r14d,ebx
   29a10:	and    r14d,esi
   29a13:	mov    ebp,r15d
   29a16:	and    ebp,ebx
   29a18:	xor    ebp,r14d
   29a1b:	add    ebp,r11d
   29a1e:	add    ebp,r9d
   29a21:	mov    edi,DWORD PTR [rsp+0x34]
   29a25:	add    edi,r9d
   29a28:	mov    r9d,edi
   29a2b:	rol    r9d,0x1a
   29a2f:	mov    r11d,edi
   29a32:	rol    r11d,0x15
   29a36:	xor    r11d,r9d
   29a39:	mov    r9d,edi
   29a3c:	rol    r9d,0x7
   29a40:	xor    r9d,r11d
   29a43:	mov    r11d,r10d
   29a46:	xor    r11d,edx
   29a49:	and    r11d,edi
   29a4c:	xor    r11d,edx
   29a4f:	mov    rcx,rdx
   29a52:	add    r11d,eax
   29a55:	mov    eax,ebp
   29a57:	rol    eax,0x1e
   29a5a:	add    r9d,r11d
   29a5d:	add    r9d,0x1e376c08
   29a64:	mov    r11d,ebp
   29a67:	rol    r11d,0x13
   29a6b:	xor    r11d,eax
   29a6e:	mov    eax,ebp
   29a70:	rol    eax,0xa
   29a73:	xor    eax,r11d
   29a76:	mov    r11d,esi
   29a79:	mov    rdx,r15
   29a7c:	and    r11d,edx
   29a7f:	mov    r15d,esi
   29a82:	xor    r15d,edx
   29a85:	and    r15d,ebp
   29a88:	xor    r15d,r11d
   29a8b:	add    r15d,eax
   29a8e:	add    ebx,r9d
   29a91:	mov    eax,ebx
   29a93:	rol    eax,0x1a
   29a96:	add    r15d,r9d
   29a99:	mov    r9d,ebx
   29a9c:	rol    r9d,0x15
   29aa0:	xor    r9d,eax
   29aa3:	mov    eax,ebx
   29aa5:	rol    eax,0x7
   29aa8:	xor    eax,r9d
   29aab:	mov    r8,QWORD PTR [rsp+0x88]
   29ab3:	mov    r11d,edi
   29ab6:	xor    r11d,r10d
   29ab9:	and    r11d,ebx
   29abc:	xor    r11d,r10d
   29abf:	add    r11d,r8d
   29ac2:	add    r11d,ecx
   29ac5:	add    eax,r11d
   29ac8:	add    eax,0x2748774c
   29acd:	mov    r9d,r15d
   29ad0:	rol    r9d,0x1e
   29ad4:	mov    r11d,r15d
   29ad7:	rol    r11d,0x13
   29adb:	xor    r11d,r9d
   29ade:	mov    r9d,r15d
   29ae1:	rol    r9d,0xa
   29ae5:	xor    r9d,r11d
   29ae8:	mov    r14d,ebp
   29aeb:	xor    r14d,esi
   29aee:	and    r14d,r15d
   29af1:	mov    r11d,ebp
   29af4:	and    r11d,esi
   29af7:	xor    r11d,r14d
   29afa:	add    r11d,r9d
   29afd:	add    r11d,eax
   29b00:	add    edx,eax
   29b02:	mov    eax,edx
   29b04:	rol    eax,0x1a
   29b07:	mov    r9d,edx
   29b0a:	rol    r9d,0x15
   29b0e:	xor    r9d,eax
   29b11:	mov    eax,edx
   29b13:	rol    eax,0x7
   29b16:	xor    eax,r9d
   29b19:	mov    rcx,QWORD PTR [rsp+0x80]
   29b21:	lea    r9d,[rcx+r10*1]
   29b25:	mov    r10d,ebx
   29b28:	xor    r10d,edi
   29b2b:	and    r10d,edx
   29b2e:	xor    r10d,edi
   29b31:	add    r10d,r9d
   29b34:	mov    r9d,r11d
   29b37:	rol    r9d,0x1e
   29b3b:	add    eax,r10d
   29b3e:	add    eax,0x34b0bcb5
   29b43:	mov    r10d,r11d
   29b46:	rol    r10d,0x13
   29b4a:	xor    r10d,r9d
   29b4d:	mov    r9d,r11d
   29b50:	rol    r9d,0xa
   29b54:	xor    r9d,r10d
   29b57:	mov    r14d,r15d
   29b5a:	and    r14d,ebp
   29b5d:	mov    r10d,r15d
   29b60:	xor    r10d,ebp
   29b63:	and    r10d,r11d
   29b66:	xor    r10d,r14d
   29b69:	add    r10d,r9d
   29b6c:	add    r10d,eax
   29b6f:	mov    r9d,r8d
   29b72:	rol    r9d,0xf
   29b76:	add    esi,eax
   29b78:	mov    eax,r8d
   29b7b:	rol    eax,0xd
   29b7e:	xor    eax,r9d
   29b81:	mov    r9,QWORD PTR [rsp+0x28]
   29b86:	add    r9d,r8d
   29b89:	mov    QWORD PTR [rsp+0x28],r9
   29b8e:	mov    r9d,r8d
   29b91:	shr    r9d,0xa
   29b95:	xor    r9d,eax
   29b98:	mov    eax,ecx
   29b9a:	rol    eax,0xf
   29b9d:	add    r9d,r12d
   29ba0:	mov    r14d,ecx
   29ba3:	rol    r14d,0xd
   29ba7:	xor    r14d,eax
   29baa:	mov    rax,QWORD PTR [rsp+0x18]
   29baf:	add    eax,ecx
   29bb1:	mov    QWORD PTR [rsp+0x18],rax
   29bb6:	mov    eax,ecx
   29bb8:	shr    eax,0xa
   29bbb:	xor    eax,r14d
   29bbe:	mov    r14d,r9d
   29bc1:	rol    r14d,0xf
   29bc5:	add    eax,r13d
   29bc8:	mov    r12d,r9d
   29bcb:	rol    r12d,0xd
   29bcf:	xor    r12d,r14d
   29bd2:	add    edi,r9d
   29bd5:	add    DWORD PTR [rsp+0x48],r9d
   29bda:	mov    r13d,r9d
   29bdd:	shr    r13d,0xa
   29be1:	mov    r9d,eax
   29be4:	rol    r9d,0xf
   29be8:	xor    r13d,r12d
   29beb:	mov    r12d,eax
   29bee:	rol    r12d,0xd
   29bf2:	add    r13d,DWORD PTR [rsp+0x20]
   29bf7:	xor    r12d,r9d
   29bfa:	mov    r14d,eax
   29bfd:	shr    r14d,0xa
   29c01:	xor    r14d,r12d
   29c04:	mov    r9d,esi
   29c07:	rol    r9d,0x1a
   29c0b:	add    r14d,DWORD PTR [rsp+0x98]
   29c13:	mov    r12d,esi
   29c16:	rol    r12d,0x15
   29c1a:	xor    r12d,r9d
   29c1d:	mov    r9d,esi
   29c20:	rol    r9d,0x7
   29c24:	xor    r9d,r12d
   29c27:	mov    rcx,QWORD PTR [rsp+0x10]
   29c2c:	add    ecx,eax
   29c2e:	mov    QWORD PTR [rsp+0x10],rcx
   29c33:	add    eax,ebx
   29c35:	mov    r12d,edx
   29c38:	xor    r12d,ebx
   29c3b:	and    r12d,esi
   29c3e:	xor    r12d,ebx
   29c41:	add    r12d,edi
   29c44:	lea    edi,[r9+r12*1]
   29c48:	add    edi,0x391c0cb3
   29c4e:	mov    r8d,r10d
   29c51:	rol    r8d,0x1e
   29c55:	mov    r9d,r10d
   29c58:	rol    r9d,0x13
   29c5c:	xor    r9d,r8d
   29c5f:	mov    r12d,r10d
   29c62:	rol    r12d,0xa
   29c66:	xor    r12d,r9d
   29c69:	mov    r9d,r11d
   29c6c:	xor    r9d,r15d
   29c6f:	and    r9d,r10d
   29c72:	mov    r8d,r11d
   29c75:	and    r8d,r15d
   29c78:	xor    r8d,r9d
   29c7b:	add    r8d,r12d
   29c7e:	add    r8d,edi
   29c81:	add    ebp,edi
   29c83:	mov    edi,ebp
   29c85:	rol    edi,0x1a
   29c88:	mov    r9d,ebp
   29c8b:	rol    r9d,0x15
   29c8f:	xor    r9d,edi
   29c92:	mov    edi,ebp
   29c94:	rol    edi,0x7
   29c97:	xor    edi,r9d
   29c9a:	mov    r9d,esi
   29c9d:	xor    r9d,edx
   29ca0:	and    r9d,ebp
   29ca3:	xor    r9d,edx
   29ca6:	add    r9d,eax
   29ca9:	mov    eax,r8d
   29cac:	rol    eax,0x1e
   29caf:	add    edi,r9d
   29cb2:	add    edi,0x4ed8aa4a
   29cb8:	mov    r9d,r8d
   29cbb:	rol    r9d,0x13
   29cbf:	xor    r9d,eax
   29cc2:	mov    eax,r8d
   29cc5:	rol    eax,0xa
   29cc8:	xor    eax,r9d
   29ccb:	mov    r9d,r10d
   29cce:	and    r9d,r11d
   29cd1:	mov    ecx,r10d
   29cd4:	xor    ecx,r11d
   29cd7:	and    ecx,r8d
   29cda:	xor    ecx,r9d
   29cdd:	add    ecx,eax
   29cdf:	add    r15d,edi
   29ce2:	mov    eax,r15d
   29ce5:	rol    eax,0x1a
   29ce8:	add    ecx,edi
   29cea:	mov    edi,r15d
   29ced:	rol    edi,0x15
   29cf0:	xor    edi,eax
   29cf2:	mov    eax,r15d
   29cf5:	rol    eax,0x7
   29cf8:	xor    eax,edi
   29cfa:	mov    r9d,ebp
   29cfd:	xor    r9d,esi
   29d00:	and    r9d,r15d
   29d03:	xor    r9d,esi
   29d06:	add    r9d,r13d
   29d09:	add    r9d,edx
   29d0c:	add    eax,r9d
   29d0f:	add    eax,0x5b9cca4f
   29d14:	mov    edi,ecx
   29d16:	rol    edi,0x1e
   29d19:	mov    r9d,ecx
   29d1c:	rol    r9d,0x13
   29d20:	xor    r9d,edi
   29d23:	mov    r12d,ecx
   29d26:	rol    r12d,0xa
   29d2a:	xor    r12d,r9d
   29d2d:	mov    r9d,r8d
   29d30:	xor    r9d,r10d
   29d33:	and    r9d,ecx
   29d36:	mov    edi,r8d
   29d39:	and    edi,r10d
   29d3c:	xor    edi,r9d
   29d3f:	add    edi,r12d
   29d42:	add    edi,eax
   29d44:	add    r11d,eax
   29d47:	mov    eax,r11d
   29d4a:	rol    eax,0x1a
   29d4d:	mov    r9d,r11d
   29d50:	rol    r9d,0x15
   29d54:	xor    r9d,eax
   29d57:	mov    eax,r11d
   29d5a:	rol    eax,0x7
   29d5d:	xor    eax,r9d
   29d60:	mov    r12d,r15d
   29d63:	xor    r12d,ebp
   29d66:	and    r12d,r11d
   29d69:	xor    r12d,ebp
   29d6c:	add    r12d,r14d
   29d6f:	add    r12d,esi
   29d72:	mov    r9d,edi
   29d75:	rol    r9d,0x1e
   29d79:	add    eax,r12d
   29d7c:	add    eax,0x682e6ff3
   29d81:	mov    r12d,edi
   29d84:	rol    r12d,0x13
   29d88:	xor    r12d,r9d
   29d8b:	mov    r9d,edi
   29d8e:	rol    r9d,0xa
   29d92:	xor    r9d,r12d
   29d95:	mov    esi,ecx
   29d97:	and    esi,r8d
   29d9a:	mov    r12d,ecx
   29d9d:	xor    r12d,r8d
   29da0:	and    r12d,edi
   29da3:	xor    r12d,esi
   29da6:	add    r12d,r9d
   29da9:	add    r12d,eax
   29dac:	mov    esi,r13d
   29daf:	rol    esi,0xf
   29db2:	add    r10d,eax
   29db5:	mov    eax,r13d
   29db8:	rol    eax,0xd
   29dbb:	xor    eax,esi
   29dbd:	mov    ebx,DWORD PTR [rsp+0x40]
   29dc1:	add    ebx,r13d
   29dc4:	mov    esi,r13d
   29dc7:	shr    esi,0xa
   29dca:	xor    esi,eax
   29dcc:	mov    eax,r14d
   29dcf:	rol    eax,0xf
   29dd2:	add    esi,DWORD PTR [rsp+0x60]
   29dd6:	mov    r9d,r14d
   29dd9:	rol    r9d,0xd
   29ddd:	xor    r9d,eax
   29de0:	mov    rax,QWORD PTR [rsp]
   29de4:	add    eax,r14d
   29de7:	mov    QWORD PTR [rsp],rax
   29deb:	mov    eax,r14d
   29dee:	shr    eax,0xa
   29df1:	xor    eax,r9d
   29df4:	mov    r9d,esi
   29df7:	rol    r9d,0xf
   29dfb:	add    eax,DWORD PTR [rsp+0x28]
   29dff:	mov    r14d,esi
   29e02:	rol    r14d,0xd
   29e06:	xor    r14d,r9d
   29e09:	add    ebp,esi
   29e0b:	mov    rdx,QWORD PTR [rsp+0x8]
   29e10:	add    edx,esi
   29e12:	mov    QWORD PTR [rsp+0x8],rdx
   29e17:	mov    r13d,esi
   29e1a:	shr    r13d,0xa
   29e1e:	mov    esi,eax
   29e20:	rol    esi,0xf
   29e23:	xor    r13d,r14d
   29e26:	mov    r9d,eax
   29e29:	rol    r9d,0xd
   29e2d:	add    r13d,DWORD PTR [rsp+0x18]
   29e32:	xor    r9d,esi
   29e35:	mov    r14d,eax
   29e38:	shr    r14d,0xa
   29e3c:	xor    r14d,r9d
   29e3f:	mov    esi,r10d
   29e42:	rol    esi,0x1a
   29e45:	add    r14d,DWORD PTR [rsp+0x48]
   29e4a:	mov    edx,r10d
   29e4d:	rol    edx,0x15
   29e50:	xor    edx,esi
   29e52:	mov    esi,r10d
   29e55:	rol    esi,0x7
   29e58:	xor    esi,edx
   29e5a:	add    eax,r15d
   29e5d:	mov    edx,r11d
   29e60:	xor    edx,r15d
   29e63:	and    edx,r10d
   29e66:	xor    edx,r15d
   29e69:	add    edx,ebp
   29e6b:	add    edx,esi
   29e6d:	add    edx,0x748f82ee
   29e73:	mov    esi,r12d
   29e76:	rol    esi,0x1e
   29e79:	mov    r9d,r12d
   29e7c:	rol    r9d,0x13
   29e80:	xor    r9d,esi
   29e83:	mov    esi,r12d
   29e86:	rol    esi,0xa
   29e89:	xor    esi,r9d
   29e8c:	mov    ebp,edi
   29e8e:	xor    ebp,ecx
   29e90:	and    ebp,r12d
   29e93:	mov    r9d,edi
   29e96:	and    r9d,ecx
   29e99:	xor    r9d,ebp
   29e9c:	add    r9d,esi
   29e9f:	add    r9d,edx
   29ea2:	add    r8d,edx
   29ea5:	mov    edx,r8d
   29ea8:	rol    edx,0x1a
   29eab:	mov    esi,r8d
   29eae:	rol    esi,0x15
   29eb1:	xor    esi,edx
   29eb3:	mov    edx,r8d
   29eb6:	rol    edx,0x7
   29eb9:	xor    edx,esi
   29ebb:	mov    esi,r10d
   29ebe:	xor    esi,r11d
   29ec1:	and    esi,r8d
   29ec4:	xor    esi,r11d
   29ec7:	add    esi,eax
   29ec9:	add    edx,esi
   29ecb:	add    edx,0x78a5636f
   29ed1:	mov    eax,r9d
   29ed4:	rol    eax,0x1e
   29ed7:	mov    esi,r9d
   29eda:	rol    esi,0x13
   29edd:	xor    esi,eax
   29edf:	mov    ebp,r9d
   29ee2:	rol    ebp,0xa
   29ee5:	xor    ebp,esi
   29ee7:	mov    esi,r12d
   29eea:	and    esi,edi
   29eec:	mov    eax,r12d
   29eef:	xor    eax,edi
   29ef1:	and    eax,r9d
   29ef4:	xor    eax,esi
   29ef6:	add    eax,ebp
   29ef8:	add    eax,edx
   29efa:	add    ecx,edx
   29efc:	mov    edx,ecx
   29efe:	rol    edx,0x1a
   29f01:	mov    esi,ecx
   29f03:	rol    esi,0x15
   29f06:	xor    esi,edx
   29f08:	mov    edx,ecx
   29f0a:	rol    edx,0x7
   29f0d:	xor    edx,esi
   29f0f:	lea    esi,[r11+r13*1]
   29f13:	mov    r11d,r8d
   29f16:	xor    r11d,r10d
   29f19:	and    r11d,ecx
   29f1c:	xor    r11d,r10d
   29f1f:	mov    ebp,eax
   29f21:	rol    ebp,0x1e
   29f24:	add    r11d,esi
   29f27:	mov    esi,eax
   29f29:	rol    esi,0x13
   29f2c:	add    edx,r11d
   29f2f:	add    edx,0x84c87814
   29f35:	mov    r15d,eax
   29f38:	rol    r15d,0xa
   29f3c:	xor    esi,ebp
   29f3e:	xor    r15d,esi
   29f41:	mov    esi,r9d
   29f44:	xor    esi,r12d
   29f47:	and    esi,eax
   29f49:	mov    r11d,r9d
   29f4c:	and    r11d,r12d
   29f4f:	xor    r11d,esi
   29f52:	add    edi,edx
   29f54:	mov    esi,edi
   29f56:	rol    esi,0x1a
   29f59:	add    r11d,r15d
   29f5c:	mov    ebp,edi
   29f5e:	rol    ebp,0x15
   29f61:	add    r11d,edx
   29f64:	mov    edx,edi
   29f66:	rol    edx,0x7
   29f69:	xor    ebp,esi
   29f6b:	xor    edx,ebp
   29f6d:	lea    esi,[r14+r10*1]
   29f71:	mov    r10d,ecx
   29f74:	xor    r10d,r8d
   29f77:	and    r10d,edi
   29f7a:	xor    r10d,r8d
   29f7d:	add    r10d,esi
   29f80:	add    edx,r10d
   29f83:	add    edx,0x8cc70208
   29f89:	mov    esi,r11d
   29f8c:	rol    esi,0x1e
   29f8f:	mov    r10d,r11d
   29f92:	rol    r10d,0x13
   29f96:	xor    r10d,esi
   29f99:	mov    esi,r11d
   29f9c:	rol    esi,0xa
   29f9f:	xor    esi,r10d
   29fa2:	mov    ebp,eax
   29fa4:	and    ebp,r9d
   29fa7:	mov    r10d,eax
   29faa:	xor    r10d,r9d
   29fad:	and    r10d,r11d
   29fb0:	xor    r10d,ebp
   29fb3:	add    r10d,esi
   29fb6:	add    r10d,edx
   29fb9:	add    r12d,edx
   29fbc:	mov    edx,r13d
   29fbf:	rol    edx,0xf
   29fc2:	mov    esi,r13d
   29fc5:	rol    esi,0xd
   29fc8:	xor    esi,edx
   29fca:	shr    r13d,0xa
   29fce:	mov    edx,r14d
   29fd1:	rol    edx,0xf
   29fd4:	xor    r13d,esi
   29fd7:	mov    esi,r14d
   29fda:	rol    esi,0xd
   29fdd:	add    r13d,DWORD PTR [rsp+0x10]
   29fe2:	xor    esi,edx
   29fe4:	shr    r14d,0xa
   29fe8:	xor    r14d,esi
   29feb:	add    r14d,ebx
   29fee:	mov    edx,r13d
   29ff1:	rol    edx,0xf
   29ff4:	mov    esi,r13d
   29ff7:	rol    esi,0xd
   29ffa:	xor    esi,edx
   29ffc:	mov    edx,r14d
   29fff:	rol    edx,0xf
   2a002:	mov    r15d,r13d
   2a005:	shr    r15d,0xa
   2a009:	mov    ebp,r14d
   2a00c:	rol    ebp,0xd
   2a00f:	xor    r15d,esi
   2a012:	xor    ebp,edx
   2a014:	mov    esi,r14d
   2a017:	shr    esi,0xa
   2a01a:	xor    esi,ebp
   2a01c:	mov    edx,r12d
   2a01f:	rol    edx,0x1a
   2a022:	add    r13d,r8d
   2a025:	mov    r8d,r12d
   2a028:	rol    r8d,0x15
   2a02c:	xor    r8d,edx
   2a02f:	mov    edx,r12d
   2a032:	rol    edx,0x7
   2a035:	xor    edx,r8d
   2a038:	add    r14d,ecx
   2a03b:	mov    r8d,edi
   2a03e:	xor    r8d,ecx
   2a041:	and    r8d,r12d
   2a044:	xor    r8d,ecx
   2a047:	add    r8d,r13d
   2a04a:	lea    ecx,[rdx+r8*1]
   2a04e:	add    ecx,0x90befffa
   2a054:	mov    edx,r10d
   2a057:	rol    edx,0x1e
   2a05a:	mov    r8d,r10d
   2a05d:	rol    r8d,0x13
   2a061:	xor    r8d,edx
   2a064:	mov    ebp,r10d
   2a067:	rol    ebp,0xa
   2a06a:	xor    ebp,r8d
   2a06d:	mov    r8d,r11d
   2a070:	xor    r8d,eax
   2a073:	and    r8d,r10d
   2a076:	mov    edx,r11d
   2a079:	and    edx,eax
   2a07b:	xor    edx,r8d
   2a07e:	add    edx,ebp
   2a080:	add    edx,ecx
   2a082:	add    r9d,ecx
   2a085:	mov    ecx,r9d
   2a088:	rol    ecx,0x1a
   2a08b:	mov    r8d,r9d
   2a08e:	rol    r8d,0x15
   2a092:	xor    r8d,ecx
   2a095:	mov    ecx,r9d
   2a098:	rol    ecx,0x7
   2a09b:	xor    ecx,r8d
   2a09e:	mov    r8d,r12d
   2a0a1:	xor    r8d,edi
   2a0a4:	and    r8d,r9d
   2a0a7:	xor    r8d,edi
   2a0aa:	add    r8d,r14d
   2a0ad:	add    ecx,r8d
   2a0b0:	add    ecx,0xa4506ceb
   2a0b6:	mov    r8d,edx
   2a0b9:	rol    r8d,0x1e
   2a0bd:	mov    ebp,edx
   2a0bf:	rol    ebp,0x13
   2a0c2:	xor    ebp,r8d
   2a0c5:	mov    r14d,edx
   2a0c8:	rol    r14d,0xa
   2a0cc:	xor    r14d,ebp
   2a0cf:	mov    ebp,r10d
   2a0d2:	and    ebp,r11d
   2a0d5:	mov    r8d,r10d
   2a0d8:	xor    r8d,r11d
   2a0db:	and    r8d,edx
   2a0de:	xor    r8d,ebp
   2a0e1:	add    r8d,r14d
   2a0e4:	add    r8d,ecx
   2a0e7:	add    eax,ecx
   2a0e9:	mov    ecx,eax
   2a0eb:	rol    ecx,0x1a
   2a0ee:	mov    ebp,eax
   2a0f0:	rol    ebp,0x15
   2a0f3:	xor    ebp,ecx
   2a0f5:	mov    ecx,eax
   2a0f7:	rol    ecx,0x7
   2a0fa:	xor    ecx,ebp
   2a0fc:	mov    rbx,QWORD PTR [rsp]
   2a100:	add    ebx,r15d
   2a103:	add    ebx,edi
   2a105:	mov    edi,r9d
   2a108:	xor    edi,r12d
   2a10b:	and    edi,eax
   2a10d:	xor    edi,r12d
   2a110:	add    ebx,edi
   2a112:	lea    edi,[rcx+rbx*1]
   2a115:	add    edi,0xbef9a3f7
   2a11b:	mov    ecx,r8d
   2a11e:	rol    ecx,0x1e
   2a121:	mov    ebx,r8d
   2a124:	rol    ebx,0x13
   2a127:	xor    ebx,ecx
   2a129:	mov    ebp,r8d
   2a12c:	rol    ebp,0xa
   2a12f:	xor    ebp,ebx
   2a131:	mov    ebx,edx
   2a133:	xor    ebx,r10d
   2a136:	and    ebx,r8d
   2a139:	mov    ecx,edx
   2a13b:	and    ecx,r10d
   2a13e:	xor    ecx,ebx
   2a140:	add    ecx,ebp
   2a142:	add    ecx,edi
   2a144:	add    r11d,edi
   2a147:	mov    edi,r11d
   2a14a:	rol    edi,0x1a
   2a14d:	mov    ebx,r11d
   2a150:	rol    ebx,0x15
   2a153:	xor    ebx,edi
   2a155:	mov    edi,r11d
   2a158:	rol    edi,0x7
   2a15b:	xor    edi,ebx
   2a15d:	mov    rbx,QWORD PTR [rsp+0x8]
   2a162:	add    ebx,esi
   2a164:	add    ebx,r12d
   2a167:	mov    r14,rbx
   2a16a:	mov    esi,eax
   2a16c:	xor    esi,r9d
   2a16f:	and    esi,r11d
   2a172:	xor    esi,r9d
   2a175:	mov    ebx,ecx
   2a177:	rol    ebx,0x1e
   2a17a:	add    r14d,esi
   2a17d:	mov    ebp,ecx
   2a17f:	rol    ebp,0x13
   2a182:	lea    esi,[rdi+r14*1]
   2a186:	add    esi,0xc67178f2
   2a18c:	mov    r14d,ecx
   2a18f:	rol    r14d,0xa
   2a193:	xor    ebp,ebx
   2a195:	xor    r14d,ebp
   2a198:	mov    ebx,r8d
   2a19b:	and    ebx,edx
   2a19d:	mov    edi,r8d
   2a1a0:	xor    edi,edx
   2a1a2:	and    edi,ecx
   2a1a4:	xor    edi,ebx
   2a1a6:	add    edi,DWORD PTR [rsp+0x118]
   2a1ad:	add    edi,r14d
   2a1b0:	add    ecx,DWORD PTR [rsp+0x120]
   2a1b7:	add    edi,esi
   2a1b9:	add    r8d,DWORD PTR [rsp+0xd0]
   2a1c1:	add    edx,DWORD PTR [rsp+0xd8]
   2a1c8:	add    r10d,DWORD PTR [rsp+0x130]
   2a1d0:	add    r10d,esi
   2a1d3:	add    r11d,DWORD PTR [rsp+0x128]
   2a1db:	add    eax,DWORD PTR [rsp+0x110]
   2a1e2:	add    DWORD PTR [rsp+0xe4],r9d
   2a1ea:	mov    r9d,DWORD PTR [rsp+0xe4]
   2a1f2:	mov    rsi,QWORD PTR [rsp+0x100]
   2a1fa:	add    rsi,0x40
   2a1fe:	mov    r12d,edi
   2a201:	mov    r14d,ecx
   2a204:	mov    ebx,r8d
   2a207:	mov    QWORD PTR [rsp+0xd0],rbx
   2a20f:	mov    ebx,edx
   2a211:	mov    QWORD PTR [rsp+0xd8],rbx
   2a219:	mov    ebp,r10d
   2a21c:	mov    r13d,r11d
   2a21f:	mov    r15d,eax
   2a222:	mov    rbx,rsi
   2a225:	cmp    rsi,QWORD PTR [rsp+0x108]
   2a22d:	jne    27730 <sha2::sha256::compress256+0x90>
   2a233:	jmp    2a259 <sha2::sha256::compress256+0x2bb9>
   2a235:	mov    eax,r15d
   2a238:	mov    r11d,r13d
   2a23b:	mov    r10d,ebp
   2a23e:	mov    rcx,QWORD PTR [rsp+0xd8]
   2a246:	mov    edx,ecx
   2a248:	mov    rcx,QWORD PTR [rsp+0xd0]
   2a250:	mov    r8d,ecx
   2a253:	mov    ecx,r14d
   2a256:	mov    edi,r12d
   2a259:	mov    rsi,QWORD PTR [rsp+0xe8]
   2a261:	mov    DWORD PTR [rsi],edi
   2a263:	mov    DWORD PTR [rsi+0x4],ecx
   2a266:	mov    DWORD PTR [rsi+0x8],r8d
   2a26a:	mov    DWORD PTR [rsi+0xc],edx
   2a26d:	mov    DWORD PTR [rsi+0x10],r10d
   2a271:	mov    DWORD PTR [rsi+0x14],r11d
   2a275:	mov    DWORD PTR [rsi+0x18],eax
   2a278:	mov    DWORD PTR [rsi+0x1c],r9d
   2a27c:	add    rsp,0x138
   2a283:	pop    rbx
   2a284:	pop    r12
   2a286:	pop    r13
   2a288:	pop    r14
   2a28a:	pop    r15
   2a28c:	pop    rbp
   2a28d:	ret
   2a28e:	mov    r14,rdx
   2a291:	call   2a2d0 <sha2::sha256::x86::shani_cpuid::init_get::init_inner>
   2a296:	mov    rdx,r14
   2a299:	test   al,al
   2a29b:	je     276d9 <sha2::sha256::compress256+0x39>
   2a2a1:	mov    rdi,QWORD PTR [rsp+0xe8]
   2a2a9:	mov    rsi,rbx
   2a2ac:	add    rsp,0x138
   2a2b3:	pop    rbx
   2a2b4:	pop    r12
   2a2b6:	pop    r13
   2a2b8:	pop    r14
   2a2ba:	pop    r15
   2a2bc:	pop    rbp
   2a2bd:	jmp    2a320 <sha2::sha256::x86::digest_blocks>
   2a2c2:	int3
   2a2c3:	int3
   2a2c4:	int3
   2a2c5:	int3
   2a2c6:	int3
   2a2c7:	int3
   2a2c8:	int3
   2a2c9:	int3
   2a2ca:	int3
   2a2cb:	int3
   2a2cc:	int3
   2a2cd:	int3
   2a2ce:	int3
   2a2cf:	int3

000000000002a320 <sha2::sha256::x86::digest_blocks>:
   2a320:	movdqu xmm0,XMMWORD PTR [rdi]
   2a324:	movdqu xmm1,XMMWORD PTR [rdi+0x10]
   2a329:	pshufd xmm0,xmm0,0xb1
   2a32e:	pshufd xmm12,xmm1,0x1b
   2a334:	movdqa xmm13,xmm0
   2a339:	palignr xmm13,xmm12,0x8
   2a340:	pblendw xmm12,xmm0,0xf0
   2a347:	test   rdx,rdx
   2a34a:	je     2a6b6 <sha2::sha256::x86::digest_blocks+0x396>
   2a350:	shl    rdx,0x6
   2a354:	add    rdx,rsi
   2a357:	movdqa xmm5,XMMWORD PTR [rip+0xfffffffffffee581]        # 188e0 <anon.3bf34360074acd75cadd6d98e3825a38.6.llvm.5796641766152556861+0x10c9>
   2a35f:	movdqa xmm9,XMMWORD PTR [rip+0xfffffffffffee318]        # 18680 <anon.3bf34360074acd75cadd6d98e3825a38.6.llvm.5796641766152556861+0xe69>
   2a368:	movdqa xmm10,XMMWORD PTR [rip+0xfffffffffffee40f]        # 18780 <anon.3bf34360074acd75cadd6d98e3825a38.6.llvm.5796641766152556861+0xf69>
   2a371:	movdqa xmm11,XMMWORD PTR [rip+0xfffffffffffee386]        # 18700 <anon.3bf34360074acd75cadd6d98e3825a38.6.llvm.5796641766152556861+0xee9>
   2a37a:	nop    WORD PTR [rax+rax*1+0x0]
   2a380:	movdqu xmm7,XMMWORD PTR [rsi]
   2a384:	movdqu xmm14,XMMWORD PTR [rsi+0x10]
   2a38a:	movdqu xmm2,XMMWORD PTR [rsi+0x20]
   2a38f:	pshufb xmm7,xmm5
   2a394:	pshufb xmm14,xmm5
   2a39a:	movdqa xmm0,xmm7
   2a39e:	paddd  xmm0,XMMWORD PTR [rip+0xfffffffffffee31a]        # 186c0 <anon.3bf34360074acd75cadd6d98e3825a38.6.llvm.5796641766152556861+0xea9>
   2a3a6:	movdqa xmm3,xmm12
   2a3ab:	sha256rnds2 xmm3,xmm13,xmm0
   2a3b0:	pshufd xmm0,xmm0,0xe
   2a3b5:	movdqa xmm4,xmm13
   2a3ba:	sha256rnds2 xmm4,xmm3,xmm0
   2a3be:	movdqa xmm0,xmm14
   2a3c3:	paddd  xmm0,XMMWORD PTR [rip+0xfffffffffffee265]        # 18630 <anon.3bf34360074acd75cadd6d98e3825a38.6.llvm.5796641766152556861+0xe19>
   2a3cb:	pshufb xmm2,xmm5
   2a3d0:	sha256rnds2 xmm3,xmm4,xmm0
   2a3d4:	pshufd xmm0,xmm0,0xe
   2a3d9:	sha256rnds2 xmm4,xmm3,xmm0
   2a3dd:	movdqa xmm0,xmm2
   2a3e1:	paddd  xmm0,XMMWORD PTR [rip+0xfffffffffffee417]        # 18800 <anon.3bf34360074acd75cadd6d98e3825a38.6.llvm.5796641766152556861+0xfe9>
   2a3e9:	movdqu xmm8,XMMWORD PTR [rsi+0x30]
   2a3ef:	sha256rnds2 xmm3,xmm4,xmm0
   2a3f3:	pshufd xmm0,xmm0,0xe
   2a3f8:	pshufb xmm8,xmm5
   2a3fe:	sha256rnds2 xmm4,xmm3,xmm0
   2a402:	movdqa xmm0,xmm8
   2a407:	paddd  xmm0,XMMWORD PTR [rip+0xfffffffffffee591]        # 189a0 <anon.3bf34360074acd75cadd6d98e3825a38.6.llvm.5796641766152556861+0x1189>
   2a40f:	pshufd xmm1,xmm0,0xe
   2a414:	sha256msg1 xmm7,xmm14
   2a419:	sha256rnds2 xmm3,xmm4,xmm0
   2a41d:	movdqa xmm6,xmm8
   2a422:	palignr xmm6,xmm2,0x4
   2a428:	movdqa xmm0,xmm1
   2a42c:	sha256rnds2 xmm4,xmm3,xmm0
   2a430:	paddd  xmm6,xmm7
   2a434:	sha256msg2 xmm6,xmm8
   2a439:	movdqa xmm0,xmm6
   2a43d:	paddd  xmm0,XMMWORD PTR [rip+0xfffffffffffee47b]        # 188c0 <anon.3bf34360074acd75cadd6d98e3825a38.6.llvm.5796641766152556861+0x10a9>
   2a445:	pshufd xmm1,xmm0,0xe
   2a44a:	sha256msg1 xmm14,xmm2
   2a44f:	sha256rnds2 xmm3,xmm4,xmm0
   2a453:	movdqa xmm7,xmm6
   2a457:	palignr xmm7,xmm8,0x4
   2a45e:	movdqa xmm0,xmm1
   2a462:	sha256rnds2 xmm4,xmm3,xmm0
   2a466:	paddd  xmm7,xmm14
   2a46b:	sha256msg2 xmm7,xmm6
   2a46f:	movdqa xmm0,xmm7
   2a473:	paddd  xmm0,XMMWORD PTR [rip+0xfffffffffffee535]        # 189b0 <anon.3bf34360074acd75cadd6d98e3825a38.6.llvm.5796641766152556861+0x1199>
   2a47b:	pshufd xmm1,xmm0,0xe
   2a480:	sha256msg1 xmm2,xmm8
   2a485:	sha256rnds2 xmm3,xmm4,xmm0
   2a489:	movdqa xmm15,xmm7
   2a48e:	palignr xmm15,xmm6,0x4
   2a495:	movdqa xmm0,xmm1
   2a499:	sha256rnds2 xmm4,xmm3,xmm0
   2a49d:	paddd  xmm15,xmm2
   2a4a2:	sha256msg2 xmm15,xmm7
   2a4a7:	movdqa xmm0,xmm15
   2a4ac:	paddd  xmm0,XMMWORD PTR [rip+0xfffffffffffee35c]        # 18810 <anon.3bf34360074acd75cadd6d98e3825a38.6.llvm.5796641766152556861+0xff9>
   2a4b4:	sha256rnds2 xmm3,xmm4,xmm0
   2a4b8:	sha256msg1 xmm8,xmm6
   2a4bd:	movdqa xmm2,xmm15
   2a4c2:	palignr xmm2,xmm7,0x4
   2a4c8:	paddd  xmm2,xmm8
   2a4cd:	sha256msg2 xmm2,xmm15
   2a4d2:	pshufd xmm0,xmm0,0xe
   2a4d7:	movdqa xmm8,xmm2
   2a4dc:	paddd  xmm8,XMMWORD PTR [rip+0xfffffffffffee36b]        # 18850 <anon.3bf34360074acd75cadd6d98e3825a38.6.llvm.5796641766152556861+0x1039>
   2a4e5:	sha256rnds2 xmm4,xmm3,xmm0
   2a4e9:	movdqa xmm0,xmm8
   2a4ee:	sha256rnds2 xmm3,xmm4,xmm0
   2a4f2:	sha256msg1 xmm6,xmm7
   2a4f6:	movdqa xmm1,xmm2
   2a4fa:	palignr xmm1,xmm15,0x4
   2a501:	paddd  xmm1,xmm6
   2a505:	sha256msg2 xmm1,xmm2
   2a509:	pshufd xmm0,xmm8,0xe
   2a50f:	movdqa xmm6,xmm1
   2a513:	paddd  xmm6,XMMWORD PTR [rip+0xfffffffffffee425]        # 18940 <anon.3bf34360074acd75cadd6d98e3825a38.6.llvm.5796641766152556861+0x1129>
   2a51b:	sha256rnds2 xmm4,xmm3,xmm0
   2a51f:	movdqa xmm0,xmm6
   2a523:	sha256rnds2 xmm3,xmm4,xmm0
   2a527:	sha256msg1 xmm7,xmm15
   2a52c:	movdqa xmm14,xmm1
   2a531:	palignr xmm14,xmm2,0x4
   2a538:	paddd  xmm14,xmm7
   2a53d:	sha256msg2 xmm14,xmm1
   2a542:	pshufd xmm0,xmm6,0xe
   2a547:	movdqa xmm6,xmm14
   2a54c:	sha256msg1 xmm15,xmm2
   2a551:	sha256rnds2 xmm4,xmm3,xmm0
   2a555:	movdqa xmm7,xmm14
   2a55a:	palignr xmm7,xmm1,0x4
   2a560:	paddd  xmm7,xmm15
   2a565:	paddd  xmm6,XMMWORD PTR [rip+0xfffffffffffee2f3]        # 18860 <anon.3bf34360074acd75cadd6d98e3825a38.6.llvm.5796641766152556861+0x1049>
   2a56d:	pshufd xmm15,xmm6,0xe
   2a573:	sha256msg2 xmm7,xmm14
   2a578:	movdqa xmm0,xmm6
   2a57c:	sha256rnds2 xmm3,xmm4,xmm0
   2a580:	sha256msg1 xmm2,xmm1
   2a584:	movdqa xmm6,xmm7
   2a588:	palignr xmm6,xmm14,0x4
   2a58f:	paddd  xmm6,xmm2
   2a593:	movdqa xmm2,xmm7
   2a597:	paddd  xmm2,XMMWORD PTR [rip+0xfffffffffffee151]        # 186f0 <anon.3bf34360074acd75cadd6d98e3825a38.6.llvm.5796641766152556861+0xed9>
   2a59f:	movdqa xmm0,xmm15
   2a5a4:	sha256rnds2 xmm4,xmm3,xmm0
   2a5a8:	sha256msg2 xmm6,xmm7
   2a5ac:	sha256msg1 xmm1,xmm14
   2a5b1:	movdqa xmm0,xmm2
   2a5b5:	sha256rnds2 xmm3,xmm4,xmm0
   2a5b9:	movdqa xmm8,xmm6
   2a5be:	palignr xmm8,xmm7,0x4
   2a5c5:	paddd  xmm8,xmm1
   2a5ca:	pshufd xmm0,xmm2,0xe
   2a5cf:	movdqa xmm1,xmm6
   2a5d3:	paddd  xmm1,XMMWORD PTR [rip+0xfffffffffffee0f5]        # 186d0 <anon.3bf34360074acd75cadd6d98e3825a38.6.llvm.5796641766152556861+0xeb9>
   2a5db:	sha256rnds2 xmm4,xmm3,xmm0
   2a5df:	sha256msg2 xmm8,xmm6
   2a5e4:	sha256msg1 xmm14,xmm7
   2a5e9:	movdqa xmm0,xmm1
   2a5ed:	sha256rnds2 xmm3,xmm4,xmm0
   2a5f1:	movdqa xmm2,xmm8
   2a5f6:	palignr xmm2,xmm6,0x4
   2a5fc:	paddd  xmm2,xmm14
   2a601:	pshufd xmm0,xmm1,0xe
   2a606:	sha256msg2 xmm2,xmm8
   2a60b:	sha256msg1 xmm7,xmm6
   2a60f:	sha256rnds2 xmm4,xmm3,xmm0
   2a613:	movdqa xmm14,xmm2
   2a618:	palignr xmm14,xmm8,0x4
   2a61f:	sha256msg1 xmm6,xmm8
   2a624:	movdqa xmm0,xmm8
   2a629:	paddd  xmm0,XMMWORD PTR [rip+0xfffffffffffee13f]        # 18770 <anon.3bf34360074acd75cadd6d98e3825a38.6.llvm.5796641766152556861+0xf59>
   2a631:	sha256rnds2 xmm3,xmm4,xmm0
   2a635:	pshufd xmm0,xmm0,0xe
   2a63a:	paddd  xmm14,xmm7
   2a63f:	sha256msg2 xmm14,xmm2
   2a644:	sha256rnds2 xmm4,xmm3,xmm0
   2a648:	movdqa xmm1,xmm14
   2a64d:	palignr xmm1,xmm2,0x4
   2a653:	movdqa xmm0,xmm2
   2a657:	paddd  xmm0,xmm9
   2a65c:	sha256rnds2 xmm3,xmm4,xmm0
   2a660:	pshufd xmm0,xmm0,0xe
   2a665:	sha256rnds2 xmm4,xmm3,xmm0
   2a669:	paddd  xmm1,xmm6
   2a66d:	sha256msg2 xmm1,xmm14
   2a672:	movdqa xmm0,xmm14
   2a677:	paddd  xmm0,xmm10
   2a67c:	sha256rnds2 xmm3,xmm4,xmm0
   2a680:	pshufd xmm0,xmm0,0xe
   2a685:	sha256rnds2 xmm4,xmm3,xmm0
   2a689:	paddd  xmm1,xmm11
   2a68e:	movdqa xmm0,xmm1
   2a692:	sha256rnds2 xmm3,xmm4,xmm0
   2a696:	pshufd xmm0,xmm1,0xe
   2a69b:	sha256rnds2 xmm4,xmm3,xmm0
   2a69f:	paddd  xmm13,xmm4
   2a6a4:	paddd  xmm12,xmm3
   2a6a9:	add    rsi,0x40
   2a6ad:	cmp    rsi,rdx
   2a6b0:	jne    2a380 <sha2::sha256::x86::digest_blocks+0x60>
   2a6b6:	pshufd xmm0,xmm13,0x1b
   2a6bc:	pshufd xmm1,xmm12,0xb1
   2a6c2:	movdqa xmm2,xmm0
   2a6c6:	pblendw xmm2,xmm1,0xf0
   2a6cc:	palignr xmm1,xmm0,0x8
   2a6d2:	movdqu XMMWORD PTR [rdi],xmm2
   2a6d6:	movdqu XMMWORD PTR [rdi+0x10],xmm1
   2a6db:	ret
   2a6dc:	int3
   2a6dd:	int3
   2a6de:	int3
   2a6df:	int3
