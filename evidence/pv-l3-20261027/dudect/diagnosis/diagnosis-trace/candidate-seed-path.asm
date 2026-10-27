000000000013b8a0 <aspis_prover::state_only_hiding::SeedExpander::qm31>:
  13b8a0:	push   rbp
  13b8a1:	push   r15
  13b8a3:	push   r14
  13b8a5:	push   r13
  13b8a7:	push   r12
  13b8a9:	push   rbx
  13b8aa:	sub    rsp,0x98
  13b8b1:	mov    r14,rsi
  13b8b4:	mov    QWORD PTR [rsp+0x8],rdi
  13b8b9:	mov    rax,QWORD PTR [rsi+0x50]
  13b8bd:	mov    rcx,QWORD PTR [rsi]
  13b8c0:	mov    QWORD PTR [rsp+0x18],rcx
  13b8c5:	mov    rdx,QWORD PTR [rsi+0x28]
  13b8c9:	lea    rcx,[rsi+0x8]
  13b8cd:	mov    QWORD PTR [rsp+0x10],rcx
  13b8d2:	lea    r15,[rsi+0x30]
  13b8d6:	mov    ebx,0x10
  13b8db:	lea    r12,[rsp+0x20]
  13b8e0:	mov    ebp,0x7fffffff
  13b8e5:	data16 cs nop WORD PTR [rax+rax*1+0x0]
  13b8f0:	cmp    rax,0x8
  13b8f4:	je     13b930 <aspis_prover::state_only_hiding::SeedExpander::qm31+0x90>
  13b8f6:	lea    rdi,[rax*4+0x0]
  13b8fe:	inc    rax
  13b901:	mov    QWORD PTR [r14+0x50],rax
  13b905:	cmp    rdi,0x20
  13b909:	jae    13bd34 <aspis_prover::state_only_hiding::SeedExpander::qm31+0x494>
  13b90f:	mov    r13d,DWORD PTR [r15+rdi*1]
  13b913:	and    r13d,ebp
  13b916:	cmp    r13d,0x7fffffff
  13b91d:	je     13b9d6 <aspis_prover::state_only_hiding::SeedExpander::qm31+0x136>
  13b923:	jmp    13b9e4 <aspis_prover::state_only_hiding::SeedExpander::qm31+0x144>
  13b928:	nop    DWORD PTR [rax+rax*1+0x0]
  13b930:	mov    rax,QWORD PTR [rsp+0x10]
  13b935:	movups xmm0,XMMWORD PTR [rax]
  13b938:	movups xmm1,XMMWORD PTR [rax+0x10]
  13b93c:	movaps XMMWORD PTR [rsp+0x60],xmm1
  13b941:	movaps XMMWORD PTR [rsp+0x50],xmm0
  13b946:	mov    QWORD PTR [rsp],rdx
  13b94a:	lea    rax,[rip+0xffffffffffeff5eb]        # 3af3c <anon.93b5e49d352837b62369596380fc4a46.41.llvm.8837383725297823176+0x40>
  13b951:	mov    QWORD PTR [rsp+0x20],rax
  13b956:	mov    QWORD PTR [rsp+0x28],0x27
  13b95f:	lea    rax,[rsp+0x50]
  13b964:	mov    QWORD PTR [rsp+0x30],rax
  13b969:	mov    QWORD PTR [rsp+0x38],0x20
  13b972:	mov    rax,rsp
  13b975:	mov    QWORD PTR [rsp+0x40],rax
  13b97a:	mov    QWORD PTR [rsp+0x48],0x8
  13b983:	mov    r13,rdx
  13b986:	mov    edx,0x3
  13b98b:	lea    rdi,[rsp+0x70]
  13b990:	mov    rsi,r12
  13b993:	call   QWORD PTR [rsp+0x18]
  13b997:	mov    rdx,r13
  13b99a:	movups xmm0,XMMWORD PTR [rsp+0x70]
  13b99f:	movups xmm1,XMMWORD PTR [rsp+0x80]
  13b9a7:	movups XMMWORD PTR [r15+0x10],xmm1
  13b9ac:	movups XMMWORD PTR [r15],xmm0
  13b9b0:	inc    rdx
  13b9b3:	mov    QWORD PTR [r14+0x28],rdx
  13b9b7:	mov    QWORD PTR [r14+0x50],0x1
  13b9bf:	mov    eax,0x1
  13b9c4:	xor    edi,edi
  13b9c6:	mov    r13d,DWORD PTR [r15+rdi*1]
  13b9ca:	and    r13d,ebp
  13b9cd:	cmp    r13d,0x7fffffff
  13b9d4:	jne    13b9e4 <aspis_prover::state_only_hiding::SeedExpander::qm31+0x144>
  13b9d6:	dec    rbx
  13b9d9:	jne    13b8f0 <aspis_prover::state_only_hiding::SeedExpander::qm31+0x50>
  13b9df:	jmp    13bcfe <aspis_prover::state_only_hiding::SeedExpander::qm31+0x45e>
  13b9e4:	mov    ebx,0x10
  13b9e9:	mov    ebp,0x7fffffff
  13b9ee:	xchg   ax,ax
  13b9f0:	cmp    rax,0x8
  13b9f4:	je     13ba30 <aspis_prover::state_only_hiding::SeedExpander::qm31+0x190>
  13b9f6:	lea    rdi,[rax*4+0x0]
  13b9fe:	inc    rax
  13ba01:	mov    QWORD PTR [r14+0x50],rax
  13ba05:	cmp    rdi,0x20
  13ba09:	jae    13bd34 <aspis_prover::state_only_hiding::SeedExpander::qm31+0x494>
  13ba0f:	mov    r12d,DWORD PTR [r15+rdi*1]
  13ba13:	and    r12d,ebp
  13ba16:	cmp    r12d,0x7fffffff
  13ba1d:	je     13bad8 <aspis_prover::state_only_hiding::SeedExpander::qm31+0x238>
  13ba23:	jmp    13bae6 <aspis_prover::state_only_hiding::SeedExpander::qm31+0x246>
  13ba28:	nop    DWORD PTR [rax+rax*1+0x0]
  13ba30:	mov    rax,QWORD PTR [rsp+0x10]
  13ba35:	movups xmm0,XMMWORD PTR [rax]
  13ba38:	movups xmm1,XMMWORD PTR [rax+0x10]
  13ba3c:	movaps XMMWORD PTR [rsp+0x60],xmm1
  13ba41:	movaps XMMWORD PTR [rsp+0x50],xmm0
  13ba46:	mov    QWORD PTR [rsp],rdx
  13ba4a:	lea    rax,[rip+0xffffffffffeff4eb]        # 3af3c <anon.93b5e49d352837b62369596380fc4a46.41.llvm.8837383725297823176+0x40>
  13ba51:	mov    QWORD PTR [rsp+0x20],rax
  13ba56:	mov    QWORD PTR [rsp+0x28],0x27
  13ba5f:	lea    rax,[rsp+0x50]
  13ba64:	mov    QWORD PTR [rsp+0x30],rax
  13ba69:	mov    QWORD PTR [rsp+0x38],0x20
  13ba72:	mov    rax,rsp
  13ba75:	mov    QWORD PTR [rsp+0x40],rax
  13ba7a:	mov    QWORD PTR [rsp+0x48],0x8
  13ba83:	mov    r12,rdx
  13ba86:	mov    edx,0x3
  13ba8b:	lea    rdi,[rsp+0x70]
  13ba90:	lea    rsi,[rsp+0x20]
  13ba95:	call   QWORD PTR [rsp+0x18]
  13ba99:	mov    rdx,r12
  13ba9c:	movups xmm0,XMMWORD PTR [rsp+0x70]
  13baa1:	movups xmm1,XMMWORD PTR [rsp+0x80]
  13baa9:	movups XMMWORD PTR [r15+0x10],xmm1
  13baae:	movups XMMWORD PTR [r15],xmm0
  13bab2:	inc    rdx
  13bab5:	mov    QWORD PTR [r14+0x28],rdx
  13bab9:	mov    QWORD PTR [r14+0x50],0x1
  13bac1:	mov    eax,0x1
  13bac6:	xor    edi,edi
  13bac8:	mov    r12d,DWORD PTR [r15+rdi*1]
  13bacc:	and    r12d,ebp
  13bacf:	cmp    r12d,0x7fffffff
  13bad6:	jne    13bae6 <aspis_prover::state_only_hiding::SeedExpander::qm31+0x246>
  13bad8:	dec    rbx
  13badb:	jne    13b9f0 <aspis_prover::state_only_hiding::SeedExpander::qm31+0x150>
  13bae1:	jmp    13bcfe <aspis_prover::state_only_hiding::SeedExpander::qm31+0x45e>
  13bae6:	mov    ebp,0x10
  13baeb:	mov    ecx,0x7fffffff
  13baf0:	cmp    rax,0x8
  13baf4:	je     13bb30 <aspis_prover::state_only_hiding::SeedExpander::qm31+0x290>
  13baf6:	lea    rdi,[rax*4+0x0]
  13bafe:	inc    rax
  13bb01:	mov    QWORD PTR [r14+0x50],rax
  13bb05:	cmp    rdi,0x20
  13bb09:	jae    13bd34 <aspis_prover::state_only_hiding::SeedExpander::qm31+0x494>
  13bb0f:	mov    ebx,DWORD PTR [r15+rdi*1]
  13bb13:	and    ebx,ecx
  13bb15:	cmp    ebx,0x7fffffff
  13bb1b:	je     13bbdb <aspis_prover::state_only_hiding::SeedExpander::qm31+0x33b>
  13bb21:	jmp    13bbe9 <aspis_prover::state_only_hiding::SeedExpander::qm31+0x349>
  13bb26:	cs nop WORD PTR [rax+rax*1+0x0]
  13bb30:	mov    rax,QWORD PTR [rsp+0x10]
  13bb35:	movups xmm0,XMMWORD PTR [rax]
  13bb38:	movups xmm1,XMMWORD PTR [rax+0x10]
  13bb3c:	movaps XMMWORD PTR [rsp+0x60],xmm1
  13bb41:	movaps XMMWORD PTR [rsp+0x50],xmm0
  13bb46:	mov    QWORD PTR [rsp],rdx
  13bb4a:	lea    rax,[rip+0xffffffffffeff3eb]        # 3af3c <anon.93b5e49d352837b62369596380fc4a46.41.llvm.8837383725297823176+0x40>
  13bb51:	mov    QWORD PTR [rsp+0x20],rax
  13bb56:	mov    QWORD PTR [rsp+0x28],0x27
  13bb5f:	lea    rax,[rsp+0x50]
  13bb64:	mov    QWORD PTR [rsp+0x30],rax
  13bb69:	mov    QWORD PTR [rsp+0x38],0x20
  13bb72:	mov    rax,rsp
  13bb75:	mov    QWORD PTR [rsp+0x40],rax
  13bb7a:	mov    QWORD PTR [rsp+0x48],0x8
  13bb83:	mov    rbx,rdx
  13bb86:	mov    edx,0x3
  13bb8b:	lea    rdi,[rsp+0x70]
  13bb90:	lea    rsi,[rsp+0x20]
  13bb95:	call   QWORD PTR [rsp+0x18]
  13bb99:	mov    ecx,0x7fffffff
  13bb9e:	mov    rdx,rbx
  13bba1:	movups xmm0,XMMWORD PTR [rsp+0x70]
  13bba6:	movups xmm1,XMMWORD PTR [rsp+0x80]
  13bbae:	movups XMMWORD PTR [r15+0x10],xmm1
  13bbb3:	movups XMMWORD PTR [r15],xmm0
  13bbb7:	inc    rdx
  13bbba:	mov    QWORD PTR [r14+0x28],rdx
  13bbbe:	mov    QWORD PTR [r14+0x50],0x1
  13bbc6:	mov    eax,0x1
  13bbcb:	xor    edi,edi
  13bbcd:	mov    ebx,DWORD PTR [r15+rdi*1]
  13bbd1:	and    ebx,ecx
  13bbd3:	cmp    ebx,0x7fffffff
  13bbd9:	jne    13bbe9 <aspis_prover::state_only_hiding::SeedExpander::qm31+0x349>
  13bbdb:	dec    rbp
  13bbde:	jne    13baf0 <aspis_prover::state_only_hiding::SeedExpander::qm31+0x250>
  13bbe4:	jmp    13bcfe <aspis_prover::state_only_hiding::SeedExpander::qm31+0x45e>
  13bbe9:	mov    ebp,0x10
  13bbee:	mov    esi,0x7fffffff
  13bbf3:	data16 data16 data16 cs nop WORD PTR [rax+rax*1+0x0]
  13bc00:	cmp    rax,0x8
  13bc04:	je     13bc40 <aspis_prover::state_only_hiding::SeedExpander::qm31+0x3a0>
  13bc06:	lea    rdi,[rax*4+0x0]
  13bc0e:	inc    rax
  13bc11:	mov    QWORD PTR [r14+0x50],rax
  13bc15:	cmp    rdi,0x20
  13bc19:	jae    13bd34 <aspis_prover::state_only_hiding::SeedExpander::qm31+0x494>
  13bc1f:	mov    ecx,DWORD PTR [r15+rdi*1]
  13bc23:	and    ecx,esi
  13bc25:	cmp    ecx,0x7fffffff
  13bc2b:	je     13bcf5 <aspis_prover::state_only_hiding::SeedExpander::qm31+0x455>
  13bc31:	jmp    13bd1d <aspis_prover::state_only_hiding::SeedExpander::qm31+0x47d>
  13bc36:	cs nop WORD PTR [rax+rax*1+0x0]
  13bc40:	mov    rax,QWORD PTR [rsp+0x10]
  13bc45:	movups xmm0,XMMWORD PTR [rax]
  13bc48:	movups xmm1,XMMWORD PTR [rax+0x10]
  13bc4c:	movaps XMMWORD PTR [rsp+0x60],xmm1
  13bc51:	movaps XMMWORD PTR [rsp+0x50],xmm0
  13bc56:	mov    QWORD PTR [rsp],rdx
  13bc5a:	lea    rax,[rip+0xffffffffffeff2db]        # 3af3c <anon.93b5e49d352837b62369596380fc4a46.41.llvm.8837383725297823176+0x40>
  13bc61:	mov    QWORD PTR [rsp+0x20],rax
  13bc66:	mov    QWORD PTR [rsp+0x28],0x27
  13bc6f:	lea    rax,[rsp+0x50]
  13bc74:	mov    QWORD PTR [rsp+0x30],rax
  13bc79:	mov    QWORD PTR [rsp+0x38],0x20
  13bc82:	mov    rax,rsp
  13bc85:	mov    QWORD PTR [rsp+0x40],rax
  13bc8a:	mov    QWORD PTR [rsp+0x48],0x8
  13bc93:	mov    QWORD PTR [rsp+0x90],rdx
  13bc9b:	mov    edx,0x3
  13bca0:	lea    rdi,[rsp+0x70]
  13bca5:	lea    rsi,[rsp+0x20]
  13bcaa:	call   QWORD PTR [rsp+0x18]
  13bcae:	mov    esi,0x7fffffff
  13bcb3:	mov    rdx,QWORD PTR [rsp+0x90]
  13bcbb:	movups xmm0,XMMWORD PTR [rsp+0x70]
  13bcc0:	movups xmm1,XMMWORD PTR [rsp+0x80]
  13bcc8:	movups XMMWORD PTR [r15+0x10],xmm1
  13bccd:	movups XMMWORD PTR [r15],xmm0
  13bcd1:	inc    rdx
  13bcd4:	mov    QWORD PTR [r14+0x28],rdx
  13bcd8:	mov    QWORD PTR [r14+0x50],0x1
  13bce0:	mov    eax,0x1
  13bce5:	xor    edi,edi
  13bce7:	mov    ecx,DWORD PTR [r15+rdi*1]
  13bceb:	and    ecx,esi
  13bced:	cmp    ecx,0x7fffffff
  13bcf3:	jne    13bd1d <aspis_prover::state_only_hiding::SeedExpander::qm31+0x47d>
  13bcf5:	dec    rbp
  13bcf8:	jne    13bc00 <aspis_prover::state_only_hiding::SeedExpander::qm31+0x360>
  13bcfe:	mov    rdx,QWORD PTR [rsp+0x8]
  13bd03:	mov    BYTE PTR [rdx+0x1],0x2
  13bd07:	mov    al,0x1
  13bd09:	mov    BYTE PTR [rdx],al
  13bd0b:	add    rsp,0x98
  13bd12:	pop    rbx
  13bd13:	pop    r12
  13bd15:	pop    r13
  13bd17:	pop    r14
  13bd19:	pop    r15
  13bd1b:	pop    rbp
  13bd1c:	ret
  13bd1d:	mov    rdx,QWORD PTR [rsp+0x8]
  13bd22:	mov    DWORD PTR [rdx+0x4],r13d
  13bd26:	mov    DWORD PTR [rdx+0x8],r12d
  13bd2a:	mov    DWORD PTR [rdx+0xc],ebx
  13bd2d:	mov    DWORD PTR [rdx+0x10],ecx
  13bd30:	xor    eax,eax
  13bd32:	jmp    13bd09 <aspis_prover::state_only_hiding::SeedExpander::qm31+0x469>
  13bd34:	lea    rsi,[rdi+0x4]
  13bd38:	lea    rcx,[rip+0xe6719]        # 222458 <anon.144c014deabc1ff788eba05e4c9de081.5.llvm.18047182005676867147+0x18>
  13bd3f:	mov    edx,0x20
  13bd44:	call   QWORD PTR [rip+0xea046]        # 225d90 <_DYNAMIC+0x260>
  13bd4a:	int3
  13bd4b:	int3
  13bd4c:	int3
  13bd4d:	int3
  13bd4e:	int3
  13bd4f:	int3

000000000013bee0 <aspis_prover::state_only_hiding::sample_mask_cells>:
  13bee0:	push   rbp
  13bee1:	push   r15
  13bee3:	push   r14
  13bee5:	push   r13
  13bee7:	push   r12
  13bee9:	push   rbx
  13beea:	sub    rsp,0xc8
  13bef1:	movabs rcx,0x7ffffffffffffffc
  13befb:	lea    r12,[rdx*4+0x0]
  13bf03:	mov    rax,rdx
  13bf06:	shr    rax,0x3e
  13bf0a:	setne  al
  13bf0d:	cmp    r12,rcx
  13bf10:	seta   cl
  13bf13:	or     cl,al
  13bf15:	je     13bf26 <aspis_prover::state_only_hiding::sample_mask_cells+0x46>
  13bf17:	xor    r13d,r13d
  13bf1a:	mov    rdi,r13
  13bf1d:	mov    rsi,r12
  13bf20:	call   QWORD PTR [rip+0xe9e72]        # 225d98 <_DYNAMIC+0x268>
  13bf26:	mov    r15,rsi
  13bf29:	test   r12,r12
  13bf2c:	mov    QWORD PTR [rsp+0x20],rdi
  13bf31:	je     13bf5d <aspis_prover::state_only_hiding::sample_mask_cells+0x7d>
  13bf33:	mov    rbx,rdx
  13bf36:	call   QWORD PTR [rip+0xe9e34]        # 225d70 <_DYNAMIC+0x240>
  13bf3c:	mov    r13d,0x4
  13bf42:	mov    esi,0x4
  13bf47:	mov    rdi,r12
  13bf4a:	call   QWORD PTR [rip+0xe9e28]        # 225d78 <_DYNAMIC+0x248>
  13bf50:	test   rax,rax
  13bf53:	je     13bf1a <aspis_prover::state_only_hiding::sample_mask_cells+0x3a>
  13bf55:	mov    rdx,rbx
  13bf58:	mov    rcx,rbx
  13bf5b:	jmp    13bf64 <aspis_prover::state_only_hiding::sample_mask_cells+0x84>
  13bf5d:	mov    eax,0x4
  13bf62:	xor    ecx,ecx
  13bf64:	mov    QWORD PTR [rsp+0x8],rcx
  13bf69:	mov    QWORD PTR [rsp+0x10],rax
  13bf6e:	mov    QWORD PTR [rsp+0x18],0x0
  13bf77:	test   rdx,rdx
  13bf7a:	je     13c0ee <aspis_prover::state_only_hiding::sample_mask_cells+0x20e>
  13bf80:	mov    rax,QWORD PTR [r15]
  13bf83:	mov    QWORD PTR [rsp+0x40],rax
  13bf88:	mov    rbp,QWORD PTR [r15+0x28]
  13bf8c:	lea    rax,[r15+0x8]
  13bf90:	mov    QWORD PTR [rsp+0x38],rax
  13bf95:	lea    r13,[r15+0x30]
  13bf99:	mov    rbx,QWORD PTR [r15+0x50]
  13bf9d:	xor    eax,eax
  13bf9f:	mov    QWORD PTR [rsp+0x28],rdx
  13bfa4:	mov    QWORD PTR [rsp+0x30],rax
  13bfa9:	mov    r14d,0x10
  13bfaf:	nop
  13bfb0:	cmp    rbx,0x8
  13bfb4:	jne    13c070 <aspis_prover::state_only_hiding::sample_mask_cells+0x190>
  13bfba:	mov    rax,QWORD PTR [rsp+0x38]
  13bfbf:	movups xmm0,XMMWORD PTR [rax]
  13bfc2:	movups xmm1,XMMWORD PTR [rax+0x10]
  13bfc6:	movaps XMMWORD PTR [rsp+0x90],xmm1
  13bfce:	movaps XMMWORD PTR [rsp+0x80],xmm0
  13bfd6:	mov    QWORD PTR [rsp+0x48],rbp
  13bfdb:	lea    rax,[rip+0xffffffffffefef5a]        # 3af3c <anon.93b5e49d352837b62369596380fc4a46.41.llvm.8837383725297823176+0x40>
  13bfe2:	mov    QWORD PTR [rsp+0x50],rax
  13bfe7:	mov    QWORD PTR [rsp+0x58],0x27
  13bff0:	lea    rax,[rsp+0x80]
  13bff8:	mov    QWORD PTR [rsp+0x60],rax
  13bffd:	mov    QWORD PTR [rsp+0x68],0x20
  13c006:	lea    rax,[rsp+0x48]
  13c00b:	mov    QWORD PTR [rsp+0x70],rax
  13c010:	mov    QWORD PTR [rsp+0x78],0x8
  13c019:	mov    edx,0x3
  13c01e:	lea    rdi,[rsp+0xa8]
  13c026:	lea    rsi,[rsp+0x50]
  13c02b:	call   QWORD PTR [rsp+0x40]
  13c02f:	movups xmm0,XMMWORD PTR [rsp+0xa8]
  13c037:	movups xmm1,XMMWORD PTR [rsp+0xb8]
  13c03f:	movups XMMWORD PTR [r13+0x10],xmm1
  13c044:	movups XMMWORD PTR [r13+0x0],xmm0
  13c049:	inc    rbp
  13c04c:	mov    QWORD PTR [r15+0x28],rbp
  13c050:	mov    QWORD PTR [r15+0x50],0x1
  13c058:	mov    ebx,0x1
  13c05d:	xor    edi,edi
  13c05f:	jmp    13c089 <aspis_prover::state_only_hiding::sample_mask_cells+0x1a9>
  13c061:	data16 data16 data16 data16 data16 cs nop WORD PTR [rax+rax*1+0x0]
  13c070:	lea    rdi,[rbx*4+0x0]
  13c078:	inc    rbx
  13c07b:	mov    QWORD PTR [r15+0x50],rbx
  13c07f:	cmp    rdi,0x20
  13c083:	jae    13c15c <aspis_prover::state_only_hiding::sample_mask_cells+0x27c>
  13c089:	mov    r12d,DWORD PTR [r13+rdi*1+0x0]
  13c08e:	mov    eax,0x7fffffff
  13c093:	and    r12d,eax
  13c096:	cmp    r12d,0x7fffffff
  13c09d:	jne    13c0b0 <aspis_prover::state_only_hiding::sample_mask_cells+0x1d0>
  13c09f:	dec    r14
  13c0a2:	jne    13bfb0 <aspis_prover::state_only_hiding::sample_mask_cells+0xd0>
  13c0a8:	jmp    13c10f <aspis_prover::state_only_hiding::sample_mask_cells+0x22f>
  13c0aa:	nop    WORD PTR [rax+rax*1+0x0]
  13c0b0:	mov    r14,QWORD PTR [rsp+0x18]
  13c0b5:	cmp    r14,QWORD PTR [rsp+0x8]
  13c0ba:	jne    13c0c7 <aspis_prover::state_only_hiding::sample_mask_cells+0x1e7>
  13c0bc:	lea    rdi,[rsp+0x8]
  13c0c1:	call   QWORD PTR [rip+0xea3e1]        # 2264a8 <_DYNAMIC+0x978>
  13c0c7:	mov    rax,QWORD PTR [rsp+0x10]
  13c0cc:	mov    DWORD PTR [rax+r14*4],r12d
  13c0d0:	inc    r14
  13c0d3:	mov    QWORD PTR [rsp+0x18],r14
  13c0d8:	mov    rax,QWORD PTR [rsp+0x30]
  13c0dd:	inc    rax
  13c0e0:	mov    rdx,QWORD PTR [rsp+0x28]
  13c0e5:	cmp    rax,rdx
  13c0e8:	jne    13bfa4 <aspis_prover::state_only_hiding::sample_mask_cells+0xc4>
  13c0ee:	mov    rax,QWORD PTR [rsp+0x18]
  13c0f3:	mov    rbx,QWORD PTR [rsp+0x20]
  13c0f8:	mov    QWORD PTR [rbx+0x10],rax
  13c0fc:	mov    rax,QWORD PTR [rsp+0x8]
  13c101:	mov    QWORD PTR [rbx],rax
  13c104:	mov    rax,QWORD PTR [rsp+0x10]
  13c109:	mov    QWORD PTR [rbx+0x8],rax
  13c10d:	jmp    13c147 <aspis_prover::state_only_hiding::sample_mask_cells+0x267>
  13c10f:	mov    rbx,QWORD PTR [rsp+0x20]
  13c114:	mov    BYTE PTR [rbx+0x8],0x2
  13c118:	movabs rax,0x7ffffffffffffffc
  13c122:	add    rax,0x4
  13c126:	mov    QWORD PTR [rbx],rax
  13c129:	mov    rsi,QWORD PTR [rsp+0x8]
  13c12e:	test   rsi,rsi
  13c131:	je     13c147 <aspis_prover::state_only_hiding::sample_mask_cells+0x267>
  13c133:	mov    rdi,QWORD PTR [rsp+0x10]
  13c138:	shl    rsi,0x2
  13c13c:	mov    edx,0x4
  13c141:	call   QWORD PTR [rip+0xe9c39]        # 225d80 <_DYNAMIC+0x250>
  13c147:	mov    rax,rbx
  13c14a:	add    rsp,0xc8
  13c151:	pop    rbx
  13c152:	pop    r12
  13c154:	pop    r13
  13c156:	pop    r14
  13c158:	pop    r15
  13c15a:	pop    rbp
  13c15b:	ret
  13c15c:	lea    rsi,[rdi+0x4]
  13c160:	lea    rcx,[rip+0xe62f1]        # 222458 <anon.144c014deabc1ff788eba05e4c9de081.5.llvm.18047182005676867147+0x18>
  13c167:	mov    edx,0x20
  13c16c:	call   QWORD PTR [rip+0xe9c1e]        # 225d90 <_DYNAMIC+0x260>
  13c172:	ud2
  13c174:	jmp    13c178 <aspis_prover::state_only_hiding::sample_mask_cells+0x298>
  13c176:	jmp    13c178 <aspis_prover::state_only_hiding::sample_mask_cells+0x298>
  13c178:	mov    rbx,rax
  13c17b:	mov    rsi,QWORD PTR [rsp+0x8]
  13c180:	test   rsi,rsi
  13c183:	je     13c199 <aspis_prover::state_only_hiding::sample_mask_cells+0x2b9>
  13c185:	mov    rdi,QWORD PTR [rsp+0x10]
  13c18a:	shl    rsi,0x2
  13c18e:	mov    edx,0x4
  13c193:	call   QWORD PTR [rip+0xe9be7]        # 225d80 <_DYNAMIC+0x250>
  13c199:	mov    rdi,rbx
  13c19c:	call   21bc60 <_Unwind_Resume@plt>
  13c1a1:	int3
  13c1a2:	int3
  13c1a3:	int3
  13c1a4:	int3
  13c1a5:	int3
  13c1a6:	int3
  13c1a7:	int3
  13c1a8:	int3
  13c1a9:	int3
  13c1aa:	int3
  13c1ab:	int3
  13c1ac:	int3
  13c1ad:	int3
  13c1ae:	int3
  13c1af:	int3

000000000013f940 <aspis_prover::host_hashv>:
  13f940:	push   rbp
  13f941:	push   r15
  13f943:	push   r14
  13f945:	push   r13
  13f947:	push   r12
  13f949:	push   rbx
  13f94a:	sub    rsp,0x138
  13f951:	mov    QWORD PTR [rsp+0x70],rdi
  13f956:	xorps  xmm0,xmm0
  13f959:	movups XMMWORD PTR [rsp+0x58],xmm0
  13f95e:	movups XMMWORD PTR [rsp+0x48],xmm0
  13f963:	movups XMMWORD PTR [rsp+0x38],xmm0
  13f968:	movups XMMWORD PTR [rsp+0x28],xmm0
  13f96d:	mov    BYTE PTR [rsp+0x68],0x0
  13f972:	movups xmm0,XMMWORD PTR [rip+0xffffffffffef4d27]        # 346a0 <anon.a4a2687d8431a662664f5482d85c8f29.220.llvm.8517673138391085101>
  13f979:	movaps XMMWORD PTR [rsp],xmm0
  13f97d:	movups xmm0,XMMWORD PTR [rip+0xffffffffffef4d2c]        # 346b0 <anon.a4a2687d8431a662664f5482d85c8f29.220.llvm.8517673138391085101+0x10>
  13f984:	movaps XMMWORD PTR [rsp+0x10],xmm0
  13f989:	mov    QWORD PTR [rsp+0x20],0x0
  13f992:	test   rdx,rdx
  13f995:	je     13faa4 <aspis_prover::host_hashv+0x164>
  13f99b:	mov    r14,rdx
  13f99e:	mov    r15,rsi
  13f9a1:	shl    r14,0x4
  13f9a5:	add    r14,rsi
  13f9a8:	xor    r12d,r12d
  13f9ab:	jmp    13f9dd <aspis_prover::host_hashv+0x9d>
  13f9ad:	nop    DWORD PTR [rax]
  13f9b0:	lea    rax,[rsp+0x28]
  13f9b5:	lea    rdi,[rax+r13*1]
  13f9b9:	mov    rsi,rbx
  13f9bc:	mov    rdx,rbp
  13f9bf:	call   QWORD PTR [rip+0xe63a3]        # 225d68 <memcpy@GLIBC_2.14>
  13f9c5:	add    rbp,r13
  13f9c8:	mov    r12,rbp
  13f9cb:	mov    BYTE PTR [rsp+0x68],r12b
  13f9d0:	add    r15,0x10
  13f9d4:	cmp    r15,r14
  13f9d7:	je     13faa4 <aspis_prover::host_hashv+0x164>
  13f9dd:	mov    rbx,QWORD PTR [r15]
  13f9e0:	mov    rbp,QWORD PTR [r15+0x8]
  13f9e4:	movzx  r13d,r12b
  13f9e8:	mov    edx,0x40
  13f9ed:	sub    rdx,r13
  13f9f0:	mov    r12,rbp
  13f9f3:	sub    r12,rdx
  13f9f6:	jb     13f9b0 <aspis_prover::host_hashv+0x70>
  13f9f8:	test   r13,r13
  13f9fb:	je     13fa99 <aspis_prover::host_hashv+0x159>
  13fa01:	lea    rax,[rbx+rdx*1]
  13fa05:	mov    QWORD PTR [rsp+0x78],rax
  13fa0a:	mov    rbp,r14
  13fa0d:	lea    r14,[rsp+0x28]
  13fa12:	add    r13,r14
  13fa15:	mov    rdi,r13
  13fa18:	mov    rsi,rbx
  13fa1b:	call   QWORD PTR [rip+0xe6347]        # 225d68 <memcpy@GLIBC_2.14>
  13fa21:	inc    QWORD PTR [rsp+0x20]
  13fa26:	mov    edx,0x1
  13fa2b:	mov    rdi,rsp
  13fa2e:	mov    rsi,r14
  13fa31:	mov    r14,rbp
  13fa34:	call   QWORD PTR [rip+0xe6fde]        # 226a18 <_DYNAMIC+0xee8>
  13fa3a:	mov    rbx,QWORD PTR [rsp+0x78]
  13fa3f:	cmp    r12,0x40
  13fa43:	jb     13fa5d <aspis_prover::host_hashv+0x11d>
  13fa45:	mov    rdx,r12
  13fa48:	shr    rdx,0x6
  13fa4c:	add    QWORD PTR [rsp+0x20],rdx
  13fa51:	mov    rdi,rsp
  13fa54:	mov    rsi,rbx
  13fa57:	call   QWORD PTR [rip+0xe6fbb]        # 226a18 <_DYNAMIC+0xee8>
  13fa5d:	mov    rax,r12
  13fa60:	movabs rcx,0x7fffffffffffffc0
  13fa6a:	and    rax,rcx
  13fa6d:	and    r12d,0x3f
  13fa71:	add    rbx,rax
  13fa74:	lea    rdi,[rsp+0x28]
  13fa79:	mov    rsi,rbx
  13fa7c:	mov    rdx,r12
  13fa7f:	call   QWORD PTR [rip+0xe62e3]        # 225d68 <memcpy@GLIBC_2.14>
  13fa85:	mov    BYTE PTR [rsp+0x68],r12b
  13fa8a:	add    r15,0x10
  13fa8e:	cmp    r15,r14
  13fa91:	jne    13f9dd <aspis_prover::host_hashv+0x9d>
  13fa97:	jmp    13faa4 <aspis_prover::host_hashv+0x164>
  13fa99:	mov    r12,rbp
  13fa9c:	cmp    r12,0x40
  13faa0:	jae    13fa45 <aspis_prover::host_hashv+0x105>
  13faa2:	jmp    13fa5d <aspis_prover::host_hashv+0x11d>
  13faa4:	mov    rax,QWORD PTR [rsp+0x60]
  13faa9:	mov    QWORD PTR [rsp+0xe0],rax
  13fab1:	movzx  eax,BYTE PTR [rsp+0x68]
  13fab6:	mov    BYTE PTR [rsp+0xe8],al
  13fabd:	mov    eax,DWORD PTR [rsp+0x69]
  13fac1:	mov    DWORD PTR [rsp+0xe9],eax
  13fac8:	movzx  eax,WORD PTR [rsp+0x6d]
  13facd:	mov    WORD PTR [rsp+0xed],ax
  13fad5:	movzx  eax,BYTE PTR [rsp+0x6f]
  13fada:	mov    BYTE PTR [rsp+0xef],al
  13fae1:	movdqa xmm0,XMMWORD PTR [rsp]
  13fae6:	movaps xmm1,XMMWORD PTR [rsp+0x10]
  13faeb:	mov    rax,QWORD PTR [rsp+0x20]
  13faf0:	mov    rcx,QWORD PTR [rsp+0x28]
  13faf5:	movaps xmm2,XMMWORD PTR [rsp+0x30]
  13fafa:	mov    QWORD PTR [rsp+0xa0],rax
  13fb02:	mov    QWORD PTR [rsp+0xa8],rcx
  13fb0a:	movaps xmm3,XMMWORD PTR [rsp+0x50]
  13fb0f:	movaps XMMWORD PTR [rsp+0xd0],xmm3
  13fb17:	movaps xmm3,XMMWORD PTR [rsp+0x40]
  13fb1c:	movaps XMMWORD PTR [rsp+0xc0],xmm3
  13fb24:	movaps XMMWORD PTR [rsp+0xb0],xmm2
  13fb2c:	movaps XMMWORD PTR [rsp+0x90],xmm1
  13fb34:	movdqa XMMWORD PTR [rsp+0x80],xmm0
  13fb3d:	lea    rbx,[rsp+0xa8]
  13fb45:	movzx  r14d,BYTE PTR [rsp+0xe8]
  13fb4e:	mov    rax,QWORD PTR [rsp+0xa0]
  13fb56:	shl    rax,0x9
  13fb5a:	lea    r15d,[r14*8+0x0]
  13fb62:	or     r15,rax
  13fb65:	bswap  r15
  13fb68:	mov    BYTE PTR [rsp+r14*1+0xa8],0x80
  13fb71:	cmp    r14d,0x3f
  13fb75:	je     13fb9e <aspis_prover::host_hashv+0x25e>
  13fb77:	lea    rdi,[rsp+r14*1]
  13fb7b:	add    rdi,0xa8
  13fb82:	inc    rdi
  13fb85:	mov    rdx,r14
  13fb88:	xor    rdx,0x3f
  13fb8c:	xor    esi,esi
  13fb8e:	call   QWORD PTR [rip+0xe66dc]        # 226270 <memset@GLIBC_2.2.5>
  13fb94:	xor    r14d,0x38
  13fb98:	cmp    r14d,0x7
  13fb9c:	ja     13fc03 <aspis_prover::host_hashv+0x2c3>
  13fb9e:	mov    r12,QWORD PTR [rip+0xe6e73]        # 226a18 <_DYNAMIC+0xee8>
  13fba5:	lea    r14,[rsp+0x80]
  13fbad:	mov    edx,0x1
  13fbb2:	mov    rdi,r14
  13fbb5:	mov    rsi,rbx
  13fbb8:	call   r12
  13fbbb:	pxor   xmm0,xmm0
  13fbbf:	movdqa XMMWORD PTR [rsp+0x110],xmm0
  13fbc8:	movdqa XMMWORD PTR [rsp+0x100],xmm0
  13fbd1:	movdqa XMMWORD PTR [rsp+0xf0],xmm0
  13fbda:	mov    QWORD PTR [rsp+0x120],0x0
  13fbe6:	mov    QWORD PTR [rsp+0x128],r15
  13fbee:	lea    rsi,[rsp+0xf0]
  13fbf6:	mov    edx,0x1
  13fbfb:	mov    rdi,r14
  13fbfe:	call   r12
  13fc01:	jmp    13fc21 <aspis_prover::host_hashv+0x2e1>
  13fc03:	mov    QWORD PTR [rsp+0xe0],r15
  13fc0b:	lea    rdi,[rsp+0x80]
  13fc13:	mov    edx,0x1
  13fc18:	mov    rsi,rbx
  13fc1b:	call   QWORD PTR [rip+0xe6df7]        # 226a18 <_DYNAMIC+0xee8>
  13fc21:	pxor   xmm0,xmm0
  13fc25:	movdqa xmm1,XMMWORD PTR [rsp+0x80]
  13fc2e:	movdqa xmm2,XMMWORD PTR [rsp+0x90]
  13fc37:	movdqa xmm3,xmm1
  13fc3b:	punpckhbw xmm3,xmm0
  13fc3f:	pshuflw xmm3,xmm3,0x1b
  13fc44:	pshufhw xmm3,xmm3,0x1b
  13fc49:	punpcklbw xmm1,xmm0
  13fc4d:	pshuflw xmm1,xmm1,0x1b
  13fc52:	pshufhw xmm1,xmm1,0x1b
  13fc57:	packuswb xmm1,xmm3
  13fc5b:	movdqa xmm3,xmm2
  13fc5f:	punpckhbw xmm3,xmm0
  13fc63:	pshuflw xmm3,xmm3,0x1b
  13fc68:	pshufhw xmm3,xmm3,0x1b
  13fc6d:	punpcklbw xmm2,xmm0
  13fc71:	pshuflw xmm0,xmm2,0x1b
  13fc76:	pshufhw xmm0,xmm0,0x1b
  13fc7b:	packuswb xmm0,xmm3
  13fc7f:	mov    rax,QWORD PTR [rsp+0x70]
  13fc84:	movdqu XMMWORD PTR [rax],xmm1
  13fc88:	movdqu XMMWORD PTR [rax+0x10],xmm0
  13fc8d:	add    rsp,0x138
  13fc94:	pop    rbx
  13fc95:	pop    r12
  13fc97:	pop    r13
  13fc99:	pop    r14
  13fc9b:	pop    r15
  13fc9d:	pop    rbp
  13fc9e:	ret
  13fc9f:	int3

00000000001be4a0 <sha2::sha256::compress256>:
  1be4a0:	push   rbp
  1be4a1:	push   r15
  1be4a3:	push   r14
  1be4a5:	push   r13
  1be4a7:	push   r12
  1be4a9:	push   rbx
  1be4aa:	sub    rsp,0x138
  1be4b1:	mov    rbx,rsi
  1be4b4:	mov    QWORD PTR [rsp+0xe8],rdi
  1be4bc:	movzx  eax,BYTE PTR [rip+0x6a811]        # 228cd4 <sha2::sha256::x86::shani_cpuid::STORAGE>
  1be4c3:	cmp    al,0x1
  1be4c5:	je     1c10a1 <sha2::sha256::compress256+0x2c01>
  1be4cb:	movzx  eax,al
  1be4ce:	cmp    eax,0xff
  1be4d3:	je     1c108e <sha2::sha256::compress256+0x2bee>
  1be4d9:	mov    rax,QWORD PTR [rsp+0xe8]
  1be4e1:	mov    r12d,DWORD PTR [rax]
  1be4e4:	mov    r14d,DWORD PTR [rax+0x4]
  1be4e8:	mov    ecx,DWORD PTR [rax+0x8]
  1be4eb:	mov    QWORD PTR [rsp+0xd0],rcx
  1be4f3:	mov    ecx,DWORD PTR [rax+0xc]
  1be4f6:	mov    QWORD PTR [rsp+0xd8],rcx
  1be4fe:	mov    ebp,DWORD PTR [rax+0x10]
  1be501:	mov    r13d,DWORD PTR [rax+0x14]
  1be505:	mov    r15d,DWORD PTR [rax+0x18]
  1be509:	mov    r9d,DWORD PTR [rax+0x1c]
  1be50d:	test   rdx,rdx
  1be510:	je     1c1035 <sha2::sha256::compress256+0x2b95>
  1be516:	shl    rdx,0x6
  1be51a:	add    rdx,rbx
  1be51d:	mov    QWORD PTR [rsp+0x108],rdx
  1be525:	data16 cs nop WORD PTR [rax+rax*1+0x0]
  1be530:	mov    QWORD PTR [rsp+0x120],r14
  1be538:	mov    edi,r9d
  1be53b:	mov    DWORD PTR [rsp+0xe4],r9d
  1be543:	mov    eax,DWORD PTR [rbx]
  1be545:	mov    ecx,DWORD PTR [rbx+0x4]
  1be548:	bswap  eax
  1be54a:	mov    rsi,rax
  1be54d:	mov    eax,ebp
  1be54f:	rol    eax,0x1a
  1be552:	bswap  ecx
  1be554:	mov    r8,rcx
  1be557:	mov    QWORD PTR [rsp+0x60],rcx
  1be55c:	mov    ecx,ebp
  1be55e:	rol    ecx,0x15
  1be561:	xor    ecx,eax
  1be563:	mov    eax,ebp
  1be565:	rol    eax,0x7
  1be568:	xor    eax,ecx
  1be56a:	mov    r9,r15
  1be56d:	mov    QWORD PTR [rsp+0x110],r15
  1be575:	mov    edx,r9d
  1be578:	mov    QWORD PTR [rsp+0x128],r13
  1be580:	xor    edx,r13d
  1be583:	and    edx,ebp
  1be585:	xor    edx,r9d
  1be588:	add    edx,edi
  1be58a:	add    edx,eax
  1be58c:	mov    QWORD PTR [rsp+0x48],rsi
  1be591:	lea    ecx,[rsi+rdx*1]
  1be594:	add    ecx,0x428a2f98
  1be59a:	mov    eax,r12d
  1be59d:	rol    eax,0x1e
  1be5a0:	add    edx,esi
  1be5a2:	mov    esi,r12d
  1be5a5:	rol    esi,0x13
  1be5a8:	xor    esi,eax
  1be5aa:	mov    eax,r12d
  1be5ad:	rol    eax,0xa
  1be5b0:	xor    eax,esi
  1be5b2:	mov    r10,QWORD PTR [rsp+0xd0]
  1be5ba:	mov    QWORD PTR [rsp+0xd0],r10
  1be5c2:	mov    esi,r10d
  1be5c5:	xor    esi,r14d
  1be5c8:	and    esi,r12d
  1be5cb:	mov    edi,r10d
  1be5ce:	and    edi,r14d
  1be5d1:	xor    edi,esi
  1be5d3:	add    edi,eax
  1be5d5:	mov    rax,QWORD PTR [rsp+0xd8]
  1be5dd:	mov    QWORD PTR [rsp+0xd8],rax
  1be5e5:	add    eax,edx
  1be5e7:	add    eax,0x428a2f98
  1be5ec:	mov    edx,eax
  1be5ee:	rol    edx,0x1a
  1be5f1:	add    edi,ecx
  1be5f3:	mov    ecx,eax
  1be5f5:	rol    ecx,0x15
  1be5f8:	xor    ecx,edx
  1be5fa:	mov    edx,eax
  1be5fc:	rol    edx,0x7
  1be5ff:	xor    edx,ecx
  1be601:	mov    ecx,r13d
  1be604:	xor    ecx,ebp
  1be606:	and    ecx,eax
  1be608:	xor    ecx,r13d
  1be60b:	add    ecx,r15d
  1be60e:	add    ecx,r8d
  1be611:	lea    esi,[rcx+rdx*1]
  1be614:	add    ecx,edx
  1be616:	add    ecx,0x71374491
  1be61c:	mov    edx,edi
  1be61e:	rol    edx,0x1e
  1be621:	mov    r8d,edi
  1be624:	rol    r8d,0x13
  1be628:	xor    r8d,edx
  1be62b:	mov    edx,edi
  1be62d:	rol    edx,0xa
  1be630:	xor    edx,r8d
  1be633:	mov    r8d,r14d
  1be636:	and    r8d,r12d
  1be639:	mov    r9d,r14d
  1be63c:	xor    r9d,r12d
  1be63f:	and    r9d,edi
  1be642:	xor    r9d,r8d
  1be645:	add    r9d,edx
  1be648:	add    r9d,ecx
  1be64b:	lea    ecx,[r10+rsi*1]
  1be64f:	add    ecx,0x71374491
  1be655:	mov    edx,ecx
  1be657:	rol    edx,0x1a
  1be65a:	mov    esi,ecx
  1be65c:	rol    esi,0x15
  1be65f:	xor    esi,edx
  1be661:	mov    r8d,ecx
  1be664:	rol    r8d,0x7
  1be668:	xor    r8d,esi
  1be66b:	mov    r15,rbx
  1be66e:	mov    edx,DWORD PTR [rbx+0x8]
  1be671:	bswap  edx
  1be673:	mov    QWORD PTR [rsp+0x88],rdx
  1be67b:	mov    esi,eax
  1be67d:	xor    esi,ebp
  1be67f:	and    esi,ecx
  1be681:	xor    esi,ebp
  1be683:	add    esi,r13d
  1be686:	add    esi,edx
  1be688:	mov    r10d,r9d
  1be68b:	rol    r10d,0x1e
  1be68f:	lea    ebx,[rsi+r8*1]
  1be693:	add    esi,r8d
  1be696:	add    esi,0xb5c0fbcf
  1be69c:	mov    r8d,r9d
  1be69f:	rol    r8d,0x13
  1be6a3:	xor    r8d,r10d
  1be6a6:	mov    r10d,r9d
  1be6a9:	rol    r10d,0xa
  1be6ad:	xor    r10d,r8d
  1be6b0:	mov    r8d,edi
  1be6b3:	mov    rdx,r12
  1be6b6:	xor    r8d,edx
  1be6b9:	and    r8d,r9d
  1be6bc:	mov    r11d,edi
  1be6bf:	and    r11d,edx
  1be6c2:	mov    QWORD PTR [rsp+0x118],r12
  1be6ca:	xor    r11d,r8d
  1be6cd:	add    r11d,r10d
  1be6d0:	lea    r10d,[r14+rbx*1]
  1be6d4:	add    r10d,0xb5c0fbcf
  1be6db:	mov    r8d,r10d
  1be6de:	rol    r8d,0x1a
  1be6e2:	add    r11d,esi
  1be6e5:	mov    esi,r10d
  1be6e8:	rol    esi,0x15
  1be6eb:	xor    esi,r8d
  1be6ee:	mov    r8d,r10d
  1be6f1:	rol    r8d,0x7
  1be6f5:	xor    r8d,esi
  1be6f8:	mov    esi,DWORD PTR [r15+0xc]
  1be6fc:	mov    r13,r15
  1be6ff:	bswap  esi
  1be701:	mov    QWORD PTR [rsp+0x78],rsi
  1be706:	mov    ebx,ecx
  1be708:	xor    ebx,eax
  1be70a:	and    ebx,r10d
  1be70d:	xor    ebx,eax
  1be70f:	mov    QWORD PTR [rsp+0x130],rbp
  1be717:	add    ebp,esi
  1be719:	add    ebx,ebp
  1be71b:	mov    r14d,r11d
  1be71e:	rol    r14d,0x1e
  1be722:	mov    r15d,r11d
  1be725:	rol    r15d,0x13
  1be729:	lea    r12d,[rbx+r8*1]
  1be72d:	add    r8d,ebx
  1be730:	add    r8d,0xe9b5dba5
  1be737:	mov    ebp,r11d
  1be73a:	rol    ebp,0xa
  1be73d:	xor    r15d,r14d
  1be740:	xor    ebp,r15d
  1be743:	mov    ebx,r9d
  1be746:	and    ebx,edi
  1be748:	mov    r15d,r9d
  1be74b:	xor    r15d,edi
  1be74e:	and    r15d,r11d
  1be751:	xor    r15d,ebx
  1be754:	lea    ebx,[rdx+r12*1]
  1be758:	add    ebx,0xe9b5dba5
  1be75e:	mov    r14d,ebx
  1be761:	rol    r14d,0x1a
  1be765:	add    r15d,ebp
  1be768:	mov    ebp,ebx
  1be76a:	rol    ebp,0x15
  1be76d:	add    r15d,r8d
  1be770:	mov    r8d,ebx
  1be773:	rol    r8d,0x7
  1be777:	xor    ebp,r14d
  1be77a:	xor    r8d,ebp
  1be77d:	mov    edx,DWORD PTR [r13+0x10]
  1be781:	bswap  edx
  1be783:	mov    DWORD PTR [rsp+0x58],edx
  1be787:	mov    ebp,r10d
  1be78a:	xor    ebp,ecx
  1be78c:	and    ebp,ebx
  1be78e:	xor    ebp,ecx
  1be790:	add    eax,edx
  1be792:	mov    r14d,r15d
  1be795:	rol    r14d,0x1e
  1be799:	add    eax,ebp
  1be79b:	mov    ebp,r15d
  1be79e:	rol    ebp,0x13
  1be7a1:	add    eax,r8d
  1be7a4:	add    eax,0x3956c25b
  1be7a9:	mov    r12d,r15d
  1be7ac:	rol    r12d,0xa
  1be7b0:	xor    ebp,r14d
  1be7b3:	xor    r12d,ebp
  1be7b6:	mov    ebp,r11d
  1be7b9:	xor    ebp,r9d
  1be7bc:	and    ebp,r15d
  1be7bf:	mov    r8d,r11d
  1be7c2:	and    r8d,r9d
  1be7c5:	xor    r8d,ebp
  1be7c8:	add    edi,eax
  1be7ca:	mov    ebp,edi
  1be7cc:	rol    ebp,0x1a
  1be7cf:	add    r8d,r12d
  1be7d2:	mov    r14d,edi
  1be7d5:	rol    r14d,0x15
  1be7d9:	add    r8d,eax
  1be7dc:	mov    eax,edi
  1be7de:	rol    eax,0x7
  1be7e1:	xor    r14d,ebp
  1be7e4:	xor    eax,r14d
  1be7e7:	mov    edx,DWORD PTR [r13+0x14]
  1be7eb:	bswap  edx
  1be7ed:	mov    QWORD PTR [rsp+0x50],rdx
  1be7f2:	add    ecx,edx
  1be7f4:	mov    r14d,ebx
  1be7f7:	xor    r14d,r10d
  1be7fa:	and    r14d,edi
  1be7fd:	xor    r14d,r10d
  1be800:	mov    ebp,r8d
  1be803:	rol    ebp,0x1e
  1be806:	add    r14d,ecx
  1be809:	mov    ecx,r8d
  1be80c:	rol    ecx,0x13
  1be80f:	add    eax,r14d
  1be812:	add    eax,0x59f111f1
  1be817:	mov    r14d,r8d
  1be81a:	rol    r14d,0xa
  1be81e:	xor    ecx,ebp
  1be820:	xor    r14d,ecx
  1be823:	mov    ecx,r15d
  1be826:	and    ecx,r11d
  1be829:	mov    r12d,r15d
  1be82c:	xor    r12d,r11d
  1be82f:	and    r12d,r8d
  1be832:	xor    r12d,ecx
  1be835:	add    r9d,eax
  1be838:	mov    ecx,r9d
  1be83b:	rol    ecx,0x1a
  1be83e:	add    r12d,r14d
  1be841:	mov    ebp,r9d
  1be844:	rol    ebp,0x15
  1be847:	add    r12d,eax
  1be84a:	mov    eax,r9d
  1be84d:	rol    eax,0x7
  1be850:	xor    ebp,ecx
  1be852:	xor    eax,ebp
  1be854:	mov    ecx,DWORD PTR [r13+0x18]
  1be858:	bswap  ecx
  1be85a:	mov    QWORD PTR [rsp+0x38],rcx
  1be85f:	add    ecx,r10d
  1be862:	mov    r10d,edi
  1be865:	xor    r10d,ebx
  1be868:	and    r10d,r9d
  1be86b:	xor    r10d,ebx
  1be86e:	mov    ebp,r12d
  1be871:	rol    ebp,0x1e
  1be874:	add    r10d,ecx
  1be877:	mov    ecx,r12d
  1be87a:	rol    ecx,0x13
  1be87d:	add    r10d,eax
  1be880:	add    r10d,0x923f82a4
  1be887:	mov    r14d,r12d
  1be88a:	rol    r14d,0xa
  1be88e:	xor    ecx,ebp
  1be890:	xor    r14d,ecx
  1be893:	mov    ecx,r8d
  1be896:	xor    ecx,r15d
  1be899:	and    ecx,r12d
  1be89c:	mov    eax,r8d
  1be89f:	and    eax,r15d
  1be8a2:	xor    eax,ecx
  1be8a4:	add    r11d,r10d
  1be8a7:	mov    ecx,r11d
  1be8aa:	rol    ecx,0x1a
  1be8ad:	add    eax,r14d
  1be8b0:	mov    ebp,r11d
  1be8b3:	rol    ebp,0x15
  1be8b6:	add    eax,r10d
  1be8b9:	mov    r10d,r11d
  1be8bc:	rol    r10d,0x7
  1be8c0:	xor    ebp,ecx
  1be8c2:	xor    r10d,ebp
  1be8c5:	mov    ecx,DWORD PTR [r13+0x1c]
  1be8c9:	bswap  ecx
  1be8cb:	mov    QWORD PTR [rsp+0xb0],rcx
  1be8d3:	add    ecx,ebx
  1be8d5:	mov    ebx,r9d
  1be8d8:	xor    ebx,edi
  1be8da:	and    ebx,r11d
  1be8dd:	xor    ebx,edi
  1be8df:	mov    ebp,eax
  1be8e1:	rol    ebp,0x1e
  1be8e4:	add    ebx,ecx
  1be8e6:	mov    r14d,eax
  1be8e9:	rol    r14d,0x13
  1be8ed:	lea    ecx,[r10+rbx*1]
  1be8f1:	add    ecx,0xab1c5ed5
  1be8f7:	mov    r10d,eax
  1be8fa:	rol    r10d,0xa
  1be8fe:	xor    r14d,ebp
  1be901:	xor    r10d,r14d
  1be904:	mov    ebp,r12d
  1be907:	and    ebp,r8d
  1be90a:	mov    esi,r12d
  1be90d:	xor    esi,r8d
  1be910:	and    esi,eax
  1be912:	xor    esi,ebp
  1be914:	add    r15d,ecx
  1be917:	mov    ebp,r15d
  1be91a:	rol    ebp,0x1a
  1be91d:	add    esi,r10d
  1be920:	mov    r10d,r15d
  1be923:	rol    r10d,0x15
  1be927:	add    esi,ecx
  1be929:	mov    ecx,r15d
  1be92c:	rol    ecx,0x7
  1be92f:	xor    r10d,ebp
  1be932:	xor    ecx,r10d
  1be935:	mov    rbx,r13
  1be938:	mov    edx,DWORD PTR [r13+0x20]
  1be93c:	bswap  edx
  1be93e:	mov    DWORD PTR [rsp+0xa8],edx
  1be945:	add    edi,edx
  1be947:	mov    r10d,r11d
  1be94a:	xor    r10d,r9d
  1be94d:	and    r10d,r15d
  1be950:	xor    r10d,r9d
  1be953:	mov    ebp,esi
  1be955:	rol    ebp,0x1e
  1be958:	add    r10d,edi
  1be95b:	mov    edi,esi
  1be95d:	rol    edi,0x13
  1be960:	add    ecx,r10d
  1be963:	add    ecx,0xd807aa98
  1be969:	mov    r14d,esi
  1be96c:	rol    r14d,0xa
  1be970:	xor    edi,ebp
  1be972:	xor    r14d,edi
  1be975:	mov    edi,eax
  1be977:	xor    edi,r12d
  1be97a:	and    edi,esi
  1be97c:	mov    r13d,eax
  1be97f:	and    r13d,r12d
  1be982:	xor    r13d,edi
  1be985:	add    r8d,ecx
  1be988:	mov    edi,r8d
  1be98b:	rol    edi,0x1a
  1be98e:	add    r13d,r14d
  1be991:	mov    ebp,r8d
  1be994:	rol    ebp,0x15
  1be997:	add    r13d,ecx
  1be99a:	mov    ecx,r8d
  1be99d:	rol    ecx,0x7
  1be9a0:	xor    ebp,edi
  1be9a2:	xor    ecx,ebp
  1be9a4:	mov    r10,rbx
  1be9a7:	mov    edx,DWORD PTR [rbx+0x24]
  1be9aa:	bswap  edx
  1be9ac:	mov    QWORD PTR [rsp+0x20],rdx
  1be9b1:	lea    edi,[rdx+r9*1]
  1be9b5:	mov    r9d,r15d
  1be9b8:	xor    r9d,r11d
  1be9bb:	and    r9d,r8d
  1be9be:	xor    r9d,r11d
  1be9c1:	mov    ebp,r13d
  1be9c4:	rol    ebp,0x1e
  1be9c7:	add    r9d,edi
  1be9ca:	mov    edi,r13d
  1be9cd:	rol    edi,0x13
  1be9d0:	add    r9d,ecx
  1be9d3:	add    r9d,0x12835b01
  1be9da:	mov    r14d,r13d
  1be9dd:	rol    r14d,0xa
  1be9e1:	xor    edi,ebp
  1be9e3:	xor    r14d,edi
  1be9e6:	mov    edi,esi
  1be9e8:	and    edi,eax
  1be9ea:	mov    ebx,esi
  1be9ec:	xor    ebx,eax
  1be9ee:	and    ebx,r13d
  1be9f1:	xor    ebx,edi
  1be9f3:	add    r12d,r9d
  1be9f6:	mov    edi,r12d
  1be9f9:	rol    edi,0x1a
  1be9fc:	add    ebx,r14d
  1be9ff:	mov    ebp,r12d
  1bea02:	rol    ebp,0x15
  1bea05:	add    ebx,r9d
  1bea08:	mov    r9d,r12d
  1bea0b:	rol    r9d,0x7
  1bea0f:	xor    ebp,edi
  1bea11:	xor    r9d,ebp
  1bea14:	mov    ecx,DWORD PTR [r10+0x28]
  1bea18:	mov    rdx,r10
  1bea1b:	bswap  ecx
  1bea1d:	mov    QWORD PTR [rsp+0x8],rcx
  1bea22:	lea    edi,[rcx+r11*1]
  1bea26:	mov    r11d,r8d
  1bea29:	xor    r11d,r15d
  1bea2c:	and    r11d,r12d
  1bea2f:	xor    r11d,r15d
  1bea32:	mov    ebp,ebx
  1bea34:	rol    ebp,0x1e
  1bea37:	add    r11d,edi
  1bea3a:	mov    edi,ebx
  1bea3c:	rol    edi,0x13
  1bea3f:	add    r9d,r11d
  1bea42:	add    r9d,0x243185be
  1bea49:	mov    r11d,ebx
  1bea4c:	rol    r11d,0xa
  1bea50:	xor    edi,ebp
  1bea52:	xor    r11d,edi
  1bea55:	mov    edi,r13d
  1bea58:	xor    edi,esi
  1bea5a:	and    edi,ebx
  1bea5c:	mov    r14d,r13d
  1bea5f:	and    r14d,esi
  1bea62:	xor    r14d,edi
  1bea65:	add    eax,r9d
  1bea68:	mov    edi,eax
  1bea6a:	rol    edi,0x1a
  1bea6d:	add    r14d,r11d
  1bea70:	mov    r11d,eax
  1bea73:	rol    r11d,0x15
  1bea77:	add    r14d,r9d
  1bea7a:	mov    r9d,eax
  1bea7d:	rol    r9d,0x7
  1bea81:	xor    r11d,edi
  1bea84:	xor    r9d,r11d
  1bea87:	mov    ecx,DWORD PTR [r10+0x2c]
  1bea8b:	bswap  ecx
  1bea8d:	mov    QWORD PTR [rsp+0x18],rcx
  1bea92:	lea    edi,[rcx+r15*1]
  1bea96:	mov    r11d,r12d
  1bea99:	xor    r11d,r8d
  1bea9c:	and    r11d,eax
  1bea9f:	xor    r11d,r8d
  1beaa2:	mov    ebp,r14d
  1beaa5:	rol    ebp,0x1e
  1beaa8:	add    r11d,edi
  1beaab:	mov    r15d,r14d
  1beaae:	rol    r15d,0x13
  1beab2:	lea    edi,[r9+r11*1]
  1beab6:	add    edi,0x550c7dc3
  1beabc:	mov    r9d,r14d
  1beabf:	rol    r9d,0xa
  1beac3:	xor    r15d,ebp
  1beac6:	xor    r9d,r15d
  1beac9:	mov    r11d,ebx
  1beacc:	and    r11d,r13d
  1beacf:	mov    r10d,ebx
  1bead2:	xor    r10d,r13d
  1bead5:	and    r10d,r14d
  1bead8:	xor    r10d,r11d
  1beadb:	add    esi,edi
  1beadd:	mov    r11d,esi
  1beae0:	rol    r11d,0x1a
  1beae4:	add    r10d,r9d
  1beae7:	mov    r9d,esi
  1beaea:	rol    r9d,0x15
  1beaee:	add    r10d,edi
  1beaf1:	mov    edi,esi
  1beaf3:	rol    edi,0x7
  1beaf6:	xor    r9d,r11d
  1beaf9:	xor    edi,r9d
  1beafc:	mov    QWORD PTR [rsp+0x100],rdx
  1beb04:	mov    ecx,DWORD PTR [rdx+0x30]
  1beb07:	bswap  ecx
  1beb09:	mov    DWORD PTR [rsp],ecx
  1beb0c:	add    r8d,ecx
  1beb0f:	mov    r9d,eax
  1beb12:	xor    r9d,r12d
  1beb15:	and    r9d,esi
  1beb18:	xor    r9d,r12d
  1beb1b:	mov    r11d,r10d
  1beb1e:	rol    r11d,0x1e
  1beb22:	add    r9d,r8d
  1beb25:	mov    r8d,r10d
  1beb28:	rol    r8d,0x13
  1beb2c:	add    edi,r9d
  1beb2f:	add    edi,0x72be5d74
  1beb35:	mov    r9d,r10d
  1beb38:	rol    r9d,0xa
  1beb3c:	xor    r8d,r11d
  1beb3f:	xor    r9d,r8d
  1beb42:	mov    r8d,r14d
  1beb45:	xor    r8d,ebx
  1beb48:	and    r8d,r10d
  1beb4b:	mov    ecx,r14d
  1beb4e:	and    ecx,ebx
  1beb50:	xor    ecx,r8d
  1beb53:	add    r13d,edi
  1beb56:	mov    r8d,r13d
  1beb59:	rol    r8d,0x1a
  1beb5d:	add    ecx,r9d
  1beb60:	mov    r9d,r13d
  1beb63:	rol    r9d,0x15
  1beb67:	add    ecx,edi
  1beb69:	mov    edi,r13d
  1beb6c:	rol    edi,0x7
  1beb6f:	xor    r9d,r8d
  1beb72:	xor    edi,r9d
  1beb75:	mov    edx,DWORD PTR [rdx+0x34]
  1beb78:	bswap  edx
  1beb7a:	mov    QWORD PTR [rsp+0x40],rdx
  1beb7f:	lea    r8d,[rdx+r12*1]
  1beb83:	mov    r9d,esi
  1beb86:	xor    r9d,eax
  1beb89:	and    r9d,r13d
  1beb8c:	xor    r9d,eax
  1beb8f:	mov    r11d,ecx
  1beb92:	rol    r11d,0x1e
  1beb96:	add    r9d,r8d
  1beb99:	mov    r8d,ecx
  1beb9c:	rol    r8d,0x13
  1beba0:	add    edi,r9d
  1beba3:	add    edi,0x80deb1fe
  1beba9:	mov    r15d,ecx
  1bebac:	rol    r15d,0xa
  1bebb0:	xor    r8d,r11d
  1bebb3:	xor    r15d,r8d
  1bebb6:	mov    r8d,r10d
  1bebb9:	and    r8d,r14d
  1bebbc:	mov    ebp,r10d
  1bebbf:	xor    ebp,r14d
  1bebc2:	and    ebp,ecx
  1bebc4:	xor    ebp,r8d
  1bebc7:	add    ebx,edi
  1bebc9:	mov    r8d,ebx
  1bebcc:	rol    r8d,0x1a
  1bebd0:	add    ebp,r15d
  1bebd3:	mov    r11d,ebx
  1bebd6:	rol    r11d,0x15
  1bebda:	add    ebp,edi
  1bebdc:	mov    edi,ebx
  1bebde:	rol    edi,0x7
  1bebe1:	xor    r11d,r8d
  1bebe4:	xor    edi,r11d
  1bebe7:	mov    rdx,QWORD PTR [rsp+0x100]
  1bebef:	mov    r8d,DWORD PTR [rdx+0x38]
  1bebf3:	bswap  r8d
  1bebf6:	mov    QWORD PTR [rsp+0x28],r8
  1bebfb:	add    eax,r8d
  1bebfe:	mov    r8d,r13d
  1bec01:	xor    r8d,esi
  1bec04:	and    r8d,ebx
  1bec07:	mov    QWORD PTR [rsp+0x70],rbx
  1bec0c:	xor    r8d,esi
  1bec0f:	mov    r11d,ebp
  1bec12:	rol    r11d,0x1e
  1bec16:	add    r8d,eax
  1bec19:	mov    eax,ebp
  1bec1b:	rol    eax,0x13
  1bec1e:	add    edi,r8d
  1bec21:	add    edi,0x9bdc06a7
  1bec27:	mov    r8d,ebp
  1bec2a:	rol    r8d,0xa
  1bec2e:	xor    eax,r11d
  1bec31:	xor    r8d,eax
  1bec34:	mov    eax,ecx
  1bec36:	xor    eax,r10d
  1bec39:	and    eax,ebp
  1bec3b:	mov    r9d,ecx
  1bec3e:	and    r9d,r10d
  1bec41:	xor    r9d,eax
  1bec44:	add    r14d,edi
  1bec47:	mov    eax,r14d
  1bec4a:	rol    eax,0x1a
  1bec4d:	add    r9d,r8d
  1bec50:	mov    r8d,r14d
  1bec53:	rol    r8d,0x15
  1bec57:	add    r9d,edi
  1bec5a:	mov    edi,r14d
  1bec5d:	rol    edi,0x7
  1bec60:	xor    r8d,eax
  1bec63:	xor    edi,r8d
  1bec66:	mov    r11d,DWORD PTR [rdx+0x3c]
  1bec6a:	bswap  r11d
  1bec6d:	lea    eax,[r11+rsi*1]
  1bec71:	mov    r8d,ebx
  1bec74:	xor    r8d,r13d
  1bec77:	and    r8d,r14d
  1bec7a:	xor    r8d,r13d
  1bec7d:	mov    ebx,r9d
  1bec80:	rol    ebx,0x1e
  1bec83:	add    r8d,eax
  1bec86:	mov    eax,r9d
  1bec89:	rol    eax,0x13
  1bec8c:	add    r8d,edi
  1bec8f:	add    r8d,0xc19bf174
  1bec96:	mov    r15d,r9d
  1bec99:	rol    r15d,0xa
  1bec9d:	xor    eax,ebx
  1bec9f:	xor    r15d,eax
  1beca2:	mov    eax,ebp
  1beca4:	mov    DWORD PTR [rsp+0x98],ecx
  1becab:	and    eax,ecx
  1becad:	mov    edx,ebp
  1becaf:	xor    edx,ecx
  1becb1:	and    edx,r9d
  1becb4:	xor    edx,eax
  1becb6:	add    edx,r15d
  1becb9:	mov    rcx,rdx
  1becbc:	mov    edx,DWORD PTR [rsp+0x58]
  1becc0:	mov    eax,edx
  1becc2:	rol    eax,0x19
  1becc5:	add    ecx,r8d
  1becc8:	mov    QWORD PTR [rsp+0x10],rcx
  1beccd:	mov    rdi,QWORD PTR [rsp+0x78]
  1becd2:	mov    ebx,edi
  1becd4:	rol    ebx,0x19
  1becd7:	add    r10d,r8d
  1becda:	mov    r8d,edx
  1becdd:	mov    ecx,edx
  1becdf:	rol    r8d,0xe
  1bece3:	xor    r8d,eax
  1bece6:	mov    eax,edi
  1bece8:	rol    eax,0xe
  1beceb:	xor    eax,ebx
  1beced:	mov    rsi,QWORD PTR [rsp+0x88]
  1becf5:	mov    ebx,esi
  1becf7:	rol    ebx,0x19
  1becfa:	mov    r15d,esi
  1becfd:	rol    r15d,0xe
  1bed01:	xor    r15d,ebx
  1bed04:	mov    rdx,QWORD PTR [rsp+0x60]
  1bed09:	mov    ebx,edx
  1bed0b:	rol    ebx,0x19
  1bed0e:	mov    r12d,edx
  1bed11:	rol    r12d,0xe
  1bed15:	xor    r12d,ebx
  1bed18:	mov    ebx,ecx
  1bed1a:	shr    ebx,0x3
  1bed1d:	xor    ebx,r8d
  1bed20:	mov    r8d,edi
  1bed23:	shr    r8d,0x3
  1bed27:	xor    r8d,eax
  1bed2a:	mov    eax,esi
  1bed2c:	shr    eax,0x3
  1bed2f:	xor    eax,r15d
  1bed32:	mov    r15d,edx
  1bed35:	shr    r15d,0x3
  1bed39:	xor    r15d,r12d
  1bed3c:	add    edi,DWORD PTR [rsp]
  1bed3f:	add    edi,ebx
  1bed41:	add    esi,DWORD PTR [rsp+0x18]
  1bed45:	add    esi,r8d
  1bed48:	mov    rcx,rsi
  1bed4b:	add    edx,DWORD PTR [rsp+0x8]
  1bed4f:	add    edx,eax
  1bed51:	mov    r12,rdx
  1bed54:	mov    rsi,QWORD PTR [rsp+0x28]
  1bed59:	mov    eax,esi
  1bed5b:	rol    eax,0xf
  1bed5e:	mov    rdx,QWORD PTR [rsp+0x48]
  1bed63:	add    edx,DWORD PTR [rsp+0x20]
  1bed67:	mov    r8d,esi
  1bed6a:	rol    r8d,0xd
  1bed6e:	add    edx,r15d
  1bed71:	mov    r15,rdx
  1bed74:	xor    r8d,eax
  1bed77:	mov    edx,esi
  1bed79:	shr    edx,0xa
  1bed7c:	xor    edx,r8d
  1bed7f:	mov    QWORD PTR [rsp+0x80],r11
  1bed87:	mov    eax,r11d
  1bed8a:	rol    eax,0xf
  1bed8d:	add    edx,r15d
  1bed90:	mov    r8d,r11d
  1bed93:	rol    r8d,0xd
  1bed97:	xor    r8d,eax
  1bed9a:	shr    r11d,0xa
  1bed9e:	xor    r11d,r8d
  1beda1:	add    r11d,r12d
  1beda4:	mov    eax,edx
  1beda6:	rol    eax,0xf
  1beda9:	mov    r8d,edx
  1bedac:	rol    r8d,0xd
  1bedb0:	xor    r8d,eax
  1bedb3:	mov    eax,edx
  1bedb5:	mov    ebx,edx
  1bedb7:	mov    DWORD PTR [rsp+0x78],edx
  1bedbb:	shr    eax,0xa
  1bedbe:	xor    eax,r8d
  1bedc1:	add    eax,ecx
  1bedc3:	mov    r15,rax
  1bedc6:	mov    QWORD PTR [rsp+0x48],rax
  1bedcb:	mov    eax,r11d
  1bedce:	rol    eax,0xf
  1bedd1:	mov    edx,r11d
  1bedd4:	rol    edx,0xd
  1bedd7:	xor    edx,eax
  1bedd9:	mov    eax,r11d
  1beddc:	mov    r8,r11
  1beddf:	mov    QWORD PTR [rsp+0x88],r11
  1bede7:	shr    eax,0xa
  1bedea:	mov    rcx,rax
  1beded:	mov    eax,r10d
  1bedf0:	rol    eax,0x1a
  1bedf3:	xor    ecx,edx
  1bedf5:	mov    edx,r10d
  1bedf8:	rol    edx,0x15
  1bedfb:	add    ecx,edi
  1bedfd:	mov    r12,rcx
  1bee00:	mov    QWORD PTR [rsp+0x60],rcx
  1bee05:	mov    esi,r10d
  1bee08:	rol    esi,0x7
  1bee0b:	xor    edx,eax
  1bee0d:	xor    esi,edx
  1bee0f:	add    r13d,ebx
  1bee12:	mov    eax,r14d
  1bee15:	mov    r11,QWORD PTR [rsp+0x70]
  1bee1a:	xor    eax,r11d
  1bee1d:	and    eax,r10d
  1bee20:	xor    eax,r11d
  1bee23:	add    eax,r13d
  1bee26:	add    eax,esi
  1bee28:	add    eax,0xe49b69c1
  1bee2d:	mov    rdi,QWORD PTR [rsp+0x10]
  1bee32:	mov    edx,edi
  1bee34:	rol    edx,0x1e
  1bee37:	mov    esi,edi
  1bee39:	rol    esi,0x13
  1bee3c:	xor    esi,edx
  1bee3e:	mov    edx,edi
  1bee40:	rol    edx,0xa
  1bee43:	xor    edx,esi
  1bee45:	mov    esi,r9d
  1bee48:	xor    esi,ebp
  1bee4a:	and    esi,edi
  1bee4c:	mov    ecx,r9d
  1bee4f:	and    ecx,ebp
  1bee51:	xor    ecx,esi
  1bee53:	add    ecx,edx
  1bee55:	add    ecx,eax
  1bee57:	mov    esi,ecx
  1bee59:	mov    r13d,DWORD PTR [rsp+0x98]
  1bee61:	add    r13d,eax
  1bee64:	mov    eax,r13d
  1bee67:	rol    eax,0x1a
  1bee6a:	mov    edx,r13d
  1bee6d:	rol    edx,0x15
  1bee70:	xor    edx,eax
  1bee72:	mov    eax,r13d
  1bee75:	rol    eax,0x7
  1bee78:	xor    eax,edx
  1bee7a:	lea    ecx,[r8+r11*1]
  1bee7e:	mov    edx,r10d
  1bee81:	xor    edx,r14d
  1bee84:	and    edx,r13d
  1bee87:	xor    edx,r14d
  1bee8a:	mov    r8d,esi
  1bee8d:	rol    esi,0x1e
  1bee90:	add    edx,ecx
  1bee92:	mov    ecx,r8d
  1bee95:	rol    ecx,0x13
  1bee98:	add    eax,edx
  1bee9a:	add    eax,0xefbe4786
  1bee9f:	mov    edx,r8d
  1beea2:	mov    r11d,r8d
  1beea5:	rol    edx,0xa
  1beea8:	xor    ecx,esi
  1beeaa:	xor    edx,ecx
  1beeac:	mov    ecx,edi
  1beeae:	and    ecx,r9d
  1beeb1:	mov    ebx,edi
  1beeb3:	xor    ebx,r9d
  1beeb6:	and    ebx,r8d
  1beeb9:	xor    ebx,ecx
  1beebb:	add    ebp,eax
  1beebd:	mov    ecx,ebp
  1beebf:	rol    ecx,0x1a
  1beec2:	add    ebx,edx
  1beec4:	mov    edx,ebp
  1beec6:	rol    edx,0x15
  1beec9:	add    ebx,eax
  1beecb:	mov    eax,ebp
  1beecd:	rol    eax,0x7
  1beed0:	xor    edx,ecx
  1beed2:	xor    eax,edx
  1beed4:	lea    ecx,[r15+r14*1]
  1beed8:	mov    edx,r13d
  1beedb:	xor    edx,r10d
  1beede:	and    edx,ebp
  1beee0:	mov    QWORD PTR [rsp+0x68],rbp
  1beee5:	xor    edx,r10d
  1beee8:	add    edx,ecx
  1beeea:	add    eax,edx
  1beeec:	add    eax,0xfc19dc6
  1beef1:	mov    ecx,ebx
  1beef3:	rol    ecx,0x1e
  1beef6:	mov    edx,ebx
  1beef8:	rol    edx,0x13
  1beefb:	xor    edx,ecx
  1beefd:	mov    ecx,ebx
  1beeff:	rol    ecx,0xa
  1bef02:	xor    ecx,edx
  1bef04:	mov    edx,r8d
  1bef07:	xor    edx,edi
  1bef09:	and    edx,ebx
  1bef0b:	mov    esi,r8d
  1bef0e:	and    esi,edi
  1bef10:	xor    esi,edx
  1bef12:	add    esi,ecx
  1bef14:	add    esi,eax
  1bef16:	add    r9d,eax
  1bef19:	mov    eax,r9d
  1bef1c:	rol    eax,0x1a
  1bef1f:	mov    ecx,r9d
  1bef22:	rol    ecx,0x15
  1bef25:	xor    ecx,eax
  1bef27:	mov    eax,r9d
  1bef2a:	mov    QWORD PTR [rsp+0xc0],r9
  1bef32:	rol    eax,0x7
  1bef35:	xor    eax,ecx
  1bef37:	lea    ecx,[r12+r10*1]
  1bef3b:	mov    edx,ebp
  1bef3d:	mov    DWORD PTR [rsp+0x98],r13d
  1bef45:	xor    edx,r13d
  1bef48:	and    edx,r9d
  1bef4b:	xor    edx,r13d
  1bef4e:	mov    r8d,esi
  1bef51:	rol    r8d,0x1e
  1bef55:	add    edx,ecx
  1bef57:	mov    ecx,esi
  1bef59:	rol    ecx,0x13
  1bef5c:	lea    ebp,[rax+rdx*1]
  1bef5f:	add    ebp,0x240ca1cc
  1bef65:	mov    r14d,esi
  1bef68:	mov    rdi,rsi
  1bef6b:	mov    QWORD PTR [rsp+0xa0],rsi
  1bef73:	rol    r14d,0xa
  1bef77:	xor    ecx,r8d
  1bef7a:	mov    esi,DWORD PTR [rsp+0xa8]
  1bef81:	mov    edx,esi
  1bef83:	rol    edx,0x19
  1bef86:	xor    r14d,ecx
  1bef89:	mov    rcx,QWORD PTR [rsp+0xb0]
  1bef91:	mov    r12d,ecx
  1bef94:	rol    r12d,0x19
  1bef98:	mov    rax,QWORD PTR [rsp+0x38]
  1bef9d:	mov    r8d,eax
  1befa0:	rol    r8d,0x19
  1befa4:	mov    DWORD PTR [rsp+0x94],r8d
  1befac:	mov    r15d,ebx
  1befaf:	mov    DWORD PTR [rsp+0xc8],r11d
  1befb7:	and    r15d,r11d
  1befba:	mov    r8,QWORD PTR [rsp+0x50]
  1befbf:	mov    r9d,r8d
  1befc2:	rol    r9d,0x19
  1befc6:	mov    DWORD PTR [rsp+0xb8],r9d
  1befce:	mov    r9d,esi
  1befd1:	rol    r9d,0xe
  1befd5:	mov    r13d,ebx
  1befd8:	xor    r13d,r11d
  1befdb:	mov    esi,ecx
  1befdd:	rol    esi,0xe
  1befe0:	mov    r10d,esi
  1befe3:	and    r13d,edi
  1befe6:	mov    ecx,eax
  1befe8:	rol    ecx,0xe
  1befeb:	mov    DWORD PTR [rsp+0x70],ecx
  1befef:	xor    r13d,r15d
  1beff2:	mov    eax,r8d
  1beff5:	rol    eax,0xe
  1beff8:	mov    DWORD PTR [rsp+0x34],eax
  1beffc:	add    r13d,r14d
  1befff:	mov    eax,DWORD PTR [rsp]
  1bf002:	mov    esi,eax
  1bf004:	rol    esi,0x19
  1bf007:	add    r13d,ebp
  1bf00a:	mov    rdi,QWORD PTR [rsp+0x18]
  1bf00f:	mov    ecx,edi
  1bf011:	rol    ecx,0x19
  1bf014:	mov    r8,QWORD PTR [rsp+0x10]
  1bf019:	add    r8d,ebp
  1bf01c:	mov    QWORD PTR [rsp+0x10],r8
  1bf021:	mov    r11,QWORD PTR [rsp+0x8]
  1bf026:	mov    ebp,r11d
  1bf029:	rol    ebp,0x19
  1bf02c:	xor    r9d,edx
  1bf02f:	mov    DWORD PTR [rsp+0xf0],r9d
  1bf037:	mov    rdx,QWORD PTR [rsp+0x20]
  1bf03c:	mov    r15d,edx
  1bf03f:	rol    r15d,0x19
  1bf043:	xor    r10d,r12d
  1bf046:	mov    DWORD PTR [rsp+0xfc],r10d
  1bf04e:	rol    eax,0xe
  1bf051:	mov    r8d,eax
  1bf054:	mov    eax,DWORD PTR [rsp+0x94]
  1bf05b:	xor    DWORD PTR [rsp+0x70],eax
  1bf05f:	mov    eax,edi
  1bf061:	rol    eax,0xe
  1bf064:	mov    edi,DWORD PTR [rsp+0xb8]
  1bf06b:	xor    DWORD PTR [rsp+0x34],edi
  1bf06f:	mov    r12d,r11d
  1bf072:	rol    r12d,0xe
  1bf076:	xor    r8d,esi
  1bf079:	mov    DWORD PTR [rsp+0x94],r8d
  1bf081:	mov    r14d,edx
  1bf084:	rol    r14d,0xe
  1bf088:	xor    eax,ecx
  1bf08a:	mov    DWORD PTR [rsp+0xf8],eax
  1bf091:	mov    r11d,DWORD PTR [rsp+0x78]
  1bf096:	mov    ecx,r11d
  1bf099:	rol    ecx,0x19
  1bf09c:	xor    r12d,ebp
  1bf09f:	mov    rbp,QWORD PTR [rsp+0x80]
  1bf0a7:	mov    edx,ebp
  1bf0a9:	rol    edx,0x19
  1bf0ac:	xor    r14d,r15d
  1bf0af:	mov    r15d,r11d
  1bf0b2:	rol    r15d,0xe
  1bf0b6:	xor    r15d,ecx
  1bf0b9:	mov    esi,ebp
  1bf0bb:	rol    esi,0xe
  1bf0be:	xor    esi,edx
  1bf0c0:	mov    r8,QWORD PTR [rsp+0x28]
  1bf0c5:	mov    edx,r8d
  1bf0c8:	rol    edx,0x19
  1bf0cb:	mov    edi,r8d
  1bf0ce:	rol    edi,0xe
  1bf0d1:	xor    edi,edx
  1bf0d3:	mov    r9,QWORD PTR [rsp+0x40]
  1bf0d8:	mov    edx,r9d
  1bf0db:	rol    edx,0x19
  1bf0de:	mov    r10d,r9d
  1bf0e1:	rol    r10d,0xe
  1bf0e5:	xor    r10d,edx
  1bf0e8:	mov    ecx,r11d
  1bf0eb:	shr    ecx,0x3
  1bf0ee:	xor    ecx,r15d
  1bf0f1:	mov    rdx,QWORD PTR [rsp+0x38]
  1bf0f6:	mov    r15d,edx
  1bf0f9:	add    edx,ebp
  1bf0fb:	mov    rax,rbp
  1bf0fe:	add    ecx,eax
  1bf100:	mov    DWORD PTR [rsp+0xb8],ecx
  1bf107:	shr    eax,0x3
  1bf10a:	xor    eax,esi
  1bf10c:	mov    rbp,QWORD PTR [rsp+0x50]
  1bf111:	mov    ecx,ebp
  1bf113:	add    ebp,r8d
  1bf116:	add    eax,r8d
  1bf119:	mov    QWORD PTR [rsp+0x80],rax
  1bf121:	shr    r8d,0x3
  1bf125:	xor    r8d,edi
  1bf128:	mov    rax,r9
  1bf12b:	mov    r9d,DWORD PTR [rsp+0x58]
  1bf130:	add    r9d,eax
  1bf133:	add    r8d,eax
  1bf136:	mov    QWORD PTR [rsp+0x28],r8
  1bf13b:	shr    eax,0x3
  1bf13e:	xor    eax,r10d
  1bf141:	mov    r8d,DWORD PTR [rsp]
  1bf145:	add    eax,r8d
  1bf148:	mov    QWORD PTR [rsp+0x40],rax
  1bf14d:	shr    r8d,0x3
  1bf151:	xor    r8d,DWORD PTR [rsp+0x94]
  1bf159:	mov    rax,QWORD PTR [rsp+0x18]
  1bf15e:	add    r8d,eax
  1bf161:	mov    DWORD PTR [rsp+0x94],r8d
  1bf169:	shr    eax,0x3
  1bf16c:	xor    eax,DWORD PTR [rsp+0xf8]
  1bf173:	mov    rsi,QWORD PTR [rsp+0x8]
  1bf178:	add    eax,esi
  1bf17a:	mov    QWORD PTR [rsp+0x18],rax
  1bf17f:	shr    esi,0x3
  1bf182:	xor    esi,r12d
  1bf185:	mov    rax,QWORD PTR [rsp+0x20]
  1bf18a:	add    esi,eax
  1bf18c:	mov    QWORD PTR [rsp+0x8],rsi
  1bf191:	shr    eax,0x3
  1bf194:	xor    eax,r14d
  1bf197:	mov    esi,DWORD PTR [rsp+0xa8]
  1bf19e:	add    eax,esi
  1bf1a0:	mov    QWORD PTR [rsp+0x20],rax
  1bf1a5:	mov    eax,esi
  1bf1a7:	shr    eax,0x3
  1bf1aa:	xor    eax,DWORD PTR [rsp+0xf0]
  1bf1b1:	mov    rsi,QWORD PTR [rsp+0xb0]
  1bf1b9:	add    eax,esi
  1bf1bb:	shr    esi,0x3
  1bf1be:	xor    esi,DWORD PTR [rsp+0xfc]
  1bf1c5:	shr    r15d,0x3
  1bf1c9:	xor    r15d,DWORD PTR [rsp+0x70]
  1bf1ce:	shr    ecx,0x3
  1bf1d1:	xor    ecx,DWORD PTR [rsp+0x34]
  1bf1d5:	add    edx,esi
  1bf1d7:	mov    r8,QWORD PTR [rsp+0x48]
  1bf1dc:	mov    esi,r8d
  1bf1df:	rol    esi,0xf
  1bf1e2:	add    ebp,r15d
  1bf1e5:	mov    r14d,r8d
  1bf1e8:	rol    r14d,0xd
  1bf1ec:	mov    edi,r9d
  1bf1ef:	add    edi,ecx
  1bf1f1:	xor    r14d,esi
  1bf1f4:	mov    r9d,r8d
  1bf1f7:	shr    r9d,0xa
  1bf1fb:	xor    r9d,r14d
  1bf1fe:	mov    r8,QWORD PTR [rsp+0x60]
  1bf203:	mov    ecx,r8d
  1bf206:	rol    ecx,0xf
  1bf209:	add    r9d,edi
  1bf20c:	mov    esi,r8d
  1bf20f:	rol    esi,0xd
  1bf212:	xor    esi,ecx
  1bf214:	mov    edi,r8d
  1bf217:	shr    edi,0xa
  1bf21a:	xor    edi,esi
  1bf21c:	add    edi,ebp
  1bf21e:	mov    ecx,r9d
  1bf221:	rol    ecx,0xf
  1bf224:	mov    esi,r9d
  1bf227:	rol    esi,0xd
  1bf22a:	xor    esi,ecx
  1bf22c:	mov    ecx,r9d
  1bf22f:	mov    DWORD PTR [rsp+0x38],r9d
  1bf234:	shr    ecx,0xa
  1bf237:	xor    ecx,esi
  1bf239:	add    ecx,edx
  1bf23b:	mov    r12,rcx
  1bf23e:	mov    ecx,edi
  1bf240:	rol    ecx,0xf
  1bf243:	mov    esi,edi
  1bf245:	rol    esi,0xd
  1bf248:	xor    esi,ecx
  1bf24a:	mov    ecx,edi
  1bf24c:	mov    QWORD PTR [rsp],rdi
  1bf250:	shr    ecx,0xa
  1bf253:	xor    ecx,esi
  1bf255:	add    eax,r11d
  1bf258:	add    ecx,eax
  1bf25a:	mov    r10,rcx
  1bf25d:	mov    rdx,QWORD PTR [rsp+0x10]
  1bf262:	mov    eax,edx
  1bf264:	rol    eax,0x1a
  1bf267:	mov    ecx,edx
  1bf269:	rol    ecx,0x15
  1bf26c:	xor    ecx,eax
  1bf26e:	mov    eax,edx
  1bf270:	rol    eax,0x7
  1bf273:	xor    eax,ecx
  1bf275:	mov    r8d,DWORD PTR [rsp+0x98]
  1bf27d:	add    r8d,r9d
  1bf280:	mov    r15,QWORD PTR [rsp+0xc0]
  1bf288:	mov    ecx,r15d
  1bf28b:	mov    rsi,QWORD PTR [rsp+0x68]
  1bf290:	xor    ecx,esi
  1bf292:	and    ecx,edx
  1bf294:	xor    ecx,esi
  1bf296:	mov    r9,rsi
  1bf299:	add    ecx,r8d
  1bf29c:	mov    r8,r13
  1bf29f:	mov    esi,r8d
  1bf2a2:	rol    esi,0x1e
  1bf2a5:	add    ecx,eax
  1bf2a7:	add    ecx,0x2de92c6f
  1bf2ad:	mov    eax,r8d
  1bf2b0:	rol    eax,0x13
  1bf2b3:	xor    eax,esi
  1bf2b5:	mov    esi,r8d
  1bf2b8:	rol    esi,0xa
  1bf2bb:	xor    esi,eax
  1bf2bd:	mov    rbp,QWORD PTR [rsp+0xa0]
  1bf2c5:	mov    r14d,ebp
  1bf2c8:	xor    r14d,ebx
  1bf2cb:	and    r14d,r8d
  1bf2ce:	mov    eax,ebp
  1bf2d0:	and    eax,ebx
  1bf2d2:	xor    eax,r14d
  1bf2d5:	add    eax,esi
  1bf2d7:	mov    r11d,DWORD PTR [rsp+0xc8]
  1bf2df:	add    r11d,ecx
  1bf2e2:	mov    esi,r11d
  1bf2e5:	rol    esi,0x1a
  1bf2e8:	add    eax,ecx
  1bf2ea:	mov    ecx,r11d
  1bf2ed:	rol    ecx,0x15
  1bf2f0:	xor    ecx,esi
  1bf2f2:	mov    esi,r11d
  1bf2f5:	rol    esi,0x7
  1bf2f8:	xor    esi,ecx
  1bf2fa:	lea    ecx,[rdi+r9*1]
  1bf2fe:	mov    r9d,edx
  1bf301:	mov    rdi,r15
  1bf304:	xor    r9d,edi
  1bf307:	and    r9d,r11d
  1bf30a:	xor    r9d,edi
  1bf30d:	add    r9d,ecx
  1bf310:	add    esi,r9d
  1bf313:	add    esi,0x4a7484aa
  1bf319:	mov    ecx,eax
  1bf31b:	rol    ecx,0x1e
  1bf31e:	mov    r9d,eax
  1bf321:	rol    r9d,0x13
  1bf325:	xor    r9d,ecx
  1bf328:	mov    r14d,eax
  1bf32b:	rol    r14d,0xa
  1bf32f:	xor    r14d,r9d
  1bf332:	mov    r9d,r8d
  1bf335:	and    r9d,ebp
  1bf338:	mov    ecx,r8d
  1bf33b:	xor    ecx,ebp
  1bf33d:	and    ecx,eax
  1bf33f:	xor    ecx,r9d
  1bf342:	add    ecx,r14d
  1bf345:	add    ecx,esi
  1bf347:	mov    r15,rbx
  1bf34a:	add    r15d,esi
  1bf34d:	mov    esi,r15d
  1bf350:	rol    esi,0x1a
  1bf353:	mov    r9d,r15d
  1bf356:	rol    r9d,0x15
  1bf35a:	xor    r9d,esi
  1bf35d:	mov    esi,r15d
  1bf360:	rol    esi,0x7
  1bf363:	xor    esi,r9d
  1bf366:	mov    r14d,r11d
  1bf369:	xor    r14d,edx
  1bf36c:	and    r14d,r15d
  1bf36f:	xor    r14d,edx
  1bf372:	add    r14d,r12d
  1bf375:	add    r14d,edi
  1bf378:	mov    r9d,ecx
  1bf37b:	rol    r9d,0x1e
  1bf37f:	add    esi,r14d
  1bf382:	add    esi,0x5cb0a9dc
  1bf388:	mov    r14d,ecx
  1bf38b:	rol    r14d,0x13
  1bf38f:	xor    r14d,r9d
  1bf392:	mov    r13d,ecx
  1bf395:	rol    r13d,0xa
  1bf399:	xor    r13d,r14d
  1bf39c:	mov    r14d,eax
  1bf39f:	xor    r14d,r8d
  1bf3a2:	and    r14d,ecx
  1bf3a5:	mov    r9d,eax
  1bf3a8:	and    r9d,r8d
  1bf3ab:	xor    r9d,r14d
  1bf3ae:	add    r9d,r13d
  1bf3b1:	mov    rbx,rbp
  1bf3b4:	add    ebx,esi
  1bf3b6:	mov    r14d,ebx
  1bf3b9:	rol    r14d,0x1a
  1bf3bd:	add    r9d,esi
  1bf3c0:	mov    esi,ebx
  1bf3c2:	rol    esi,0x15
  1bf3c5:	xor    esi,r14d
  1bf3c8:	mov    r14d,ebx
  1bf3cb:	rol    r14d,0x7
  1bf3cf:	xor    r14d,esi
  1bf3d2:	mov    edi,r15d
  1bf3d5:	xor    edi,r11d
  1bf3d8:	and    edi,ebx
  1bf3da:	xor    edi,r11d
  1bf3dd:	add    edi,r10d
  1bf3e0:	add    edi,edx
  1bf3e2:	lea    esi,[r14+rdi*1]
  1bf3e6:	add    esi,0x76f988da
  1bf3ec:	mov    edi,r9d
  1bf3ef:	rol    edi,0x1e
  1bf3f2:	mov    r14d,r9d
  1bf3f5:	rol    r14d,0x13
  1bf3f9:	xor    r14d,edi
  1bf3fc:	mov    r13d,r9d
  1bf3ff:	rol    r13d,0xa
  1bf403:	xor    r13d,r14d
  1bf406:	mov    r14d,ecx
  1bf409:	and    r14d,eax
  1bf40c:	mov    edi,ecx
  1bf40e:	xor    edi,eax
  1bf410:	and    edi,r9d
  1bf413:	xor    edi,r14d
  1bf416:	add    edi,r13d
  1bf419:	add    edi,esi
  1bf41b:	add    r8d,esi
  1bf41e:	mov    QWORD PTR [rsp+0x58],r12
  1bf423:	mov    esi,r12d
  1bf426:	rol    esi,0xf
  1bf429:	mov    r14d,r12d
  1bf42c:	rol    r14d,0xd
  1bf430:	xor    r14d,esi
  1bf433:	mov    ebp,r12d
  1bf436:	shr    ebp,0xa
  1bf439:	xor    ebp,r14d
  1bf43c:	mov    rdx,QWORD PTR [rsp+0x20]
  1bf441:	add    edx,DWORD PTR [rsp+0x88]
  1bf448:	add    ebp,edx
  1bf44a:	mov    rdx,r10
  1bf44d:	mov    QWORD PTR [rsp+0x50],r10
  1bf452:	mov    esi,edx
  1bf454:	rol    esi,0xf
  1bf457:	mov    r14d,edx
  1bf45a:	rol    r14d,0xd
  1bf45e:	xor    r14d,esi
  1bf461:	shr    edx,0xa
  1bf464:	xor    edx,r14d
  1bf467:	mov    rsi,QWORD PTR [rsp+0x8]
  1bf46c:	add    esi,DWORD PTR [rsp+0x48]
  1bf470:	add    edx,esi
  1bf472:	mov    esi,ebp
  1bf474:	rol    esi,0xf
  1bf477:	mov    r14d,ebp
  1bf47a:	rol    r14d,0xd
  1bf47e:	xor    r14d,esi
  1bf481:	mov    esi,ebp
  1bf483:	shr    esi,0xa
  1bf486:	xor    esi,r14d
  1bf489:	mov    r10,QWORD PTR [rsp+0x18]
  1bf48e:	add    r10d,DWORD PTR [rsp+0x60]
  1bf493:	add    esi,r10d
  1bf496:	mov    r12,rsi
  1bf499:	mov    esi,edx
  1bf49b:	rol    esi,0xf
  1bf49e:	mov    r14d,edx
  1bf4a1:	rol    r14d,0xd
  1bf4a5:	xor    r14d,esi
  1bf4a8:	mov    r13d,edx
  1bf4ab:	mov    r10,rdx
  1bf4ae:	mov    QWORD PTR [rsp+0x98],rdx
  1bf4b6:	shr    r13d,0xa
  1bf4ba:	xor    r13d,r14d
  1bf4bd:	mov    edx,DWORD PTR [rsp+0x94]
  1bf4c4:	add    edx,DWORD PTR [rsp+0x38]
  1bf4c8:	add    r13d,edx
  1bf4cb:	mov    edx,r8d
  1bf4ce:	rol    edx,0x1a
  1bf4d1:	mov    esi,r8d
  1bf4d4:	rol    esi,0x15
  1bf4d7:	xor    esi,edx
  1bf4d9:	mov    edx,r8d
  1bf4dc:	rol    edx,0x7
  1bf4df:	xor    edx,esi
  1bf4e1:	add    r11d,ebp
  1bf4e4:	mov    DWORD PTR [rsp+0x34],ebp
  1bf4e8:	mov    esi,ebx
  1bf4ea:	xor    esi,r15d
  1bf4ed:	and    esi,r8d
  1bf4f0:	xor    esi,r15d
  1bf4f3:	add    esi,r11d
  1bf4f6:	mov    r11d,edi
  1bf4f9:	rol    r11d,0x1e
  1bf4fd:	add    edx,esi
  1bf4ff:	add    edx,0x983e5152
  1bf505:	mov    esi,edi
  1bf507:	rol    esi,0x13
  1bf50a:	xor    esi,r11d
  1bf50d:	mov    r14d,edi
  1bf510:	rol    r14d,0xa
  1bf514:	xor    r14d,esi
  1bf517:	mov    esi,r9d
  1bf51a:	xor    esi,ecx
  1bf51c:	and    esi,edi
  1bf51e:	mov    r11d,r9d
  1bf521:	and    r11d,ecx
  1bf524:	xor    r11d,esi
  1bf527:	add    r11d,r14d
  1bf52a:	add    eax,edx
  1bf52c:	mov    esi,eax
  1bf52e:	rol    esi,0x1a
  1bf531:	add    r11d,edx
  1bf534:	mov    edx,eax
  1bf536:	rol    edx,0x15
  1bf539:	xor    edx,esi
  1bf53b:	mov    esi,eax
  1bf53d:	rol    esi,0x7
  1bf540:	xor    esi,edx
  1bf542:	lea    edx,[r10+r15*1]
  1bf546:	mov    r10d,r8d
  1bf549:	xor    r10d,ebx
  1bf54c:	and    r10d,eax
  1bf54f:	xor    r10d,ebx
  1bf552:	add    r10d,edx
  1bf555:	lea    edx,[rsi+r10*1]
  1bf559:	add    edx,0xa831c66d
  1bf55f:	mov    esi,r11d
  1bf562:	rol    esi,0x1e
  1bf565:	mov    r10d,r11d
  1bf568:	rol    r10d,0x13
  1bf56c:	xor    r10d,esi
  1bf56f:	mov    r14d,r11d
  1bf572:	rol    r14d,0xa
  1bf576:	xor    r14d,r10d
  1bf579:	mov    r10d,edi
  1bf57c:	and    r10d,r9d
  1bf57f:	mov    r15d,edi
  1bf582:	xor    r15d,r9d
  1bf585:	and    r15d,r11d
  1bf588:	xor    r15d,r10d
  1bf58b:	add    r15d,r14d
  1bf58e:	add    r15d,edx
  1bf591:	add    ecx,edx
  1bf593:	mov    edx,ecx
  1bf595:	rol    edx,0x1a
  1bf598:	mov    r10d,ecx
  1bf59b:	rol    r10d,0x15
  1bf59f:	xor    r10d,edx
  1bf5a2:	mov    edx,ecx
  1bf5a4:	rol    edx,0x7
  1bf5a7:	xor    edx,r10d
  1bf5aa:	lea    r10d,[r12+rbx*1]
  1bf5ae:	mov    ebx,eax
  1bf5b0:	xor    ebx,r8d
  1bf5b3:	and    ebx,ecx
  1bf5b5:	xor    ebx,r8d
  1bf5b8:	add    ebx,r10d
  1bf5bb:	mov    r10d,r15d
  1bf5be:	rol    r10d,0x1e
  1bf5c2:	add    edx,ebx
  1bf5c4:	add    edx,0xb00327c8
  1bf5ca:	mov    ebx,r15d
  1bf5cd:	rol    ebx,0x13
  1bf5d0:	xor    ebx,r10d
  1bf5d3:	mov    r10d,r15d
  1bf5d6:	rol    r10d,0xa
  1bf5da:	xor    r10d,ebx
  1bf5dd:	mov    ebx,r11d
  1bf5e0:	xor    ebx,edi
  1bf5e2:	and    ebx,r15d
  1bf5e5:	mov    r14d,r11d
  1bf5e8:	and    r14d,edi
  1bf5eb:	xor    r14d,ebx
  1bf5ee:	add    r14d,r10d
  1bf5f1:	add    r9d,edx
  1bf5f4:	mov    r10d,r9d
  1bf5f7:	rol    r10d,0x1a
  1bf5fb:	add    r14d,edx
  1bf5fe:	mov    edx,r9d
  1bf601:	rol    edx,0x15
  1bf604:	xor    edx,r10d
  1bf607:	mov    r10d,r9d
  1bf60a:	rol    r10d,0x7
  1bf60e:	xor    r10d,edx
  1bf611:	lea    edx,[r8+r13*1]
  1bf615:	mov    r8d,ecx
  1bf618:	xor    r8d,eax
  1bf61b:	and    r8d,r9d
  1bf61e:	xor    r8d,eax
  1bf621:	add    r8d,edx
  1bf624:	lea    edx,[r10+r8*1]
  1bf628:	add    edx,0xbf597fc7
  1bf62e:	mov    r8d,r14d
  1bf631:	rol    r8d,0x1e
  1bf635:	mov    r10d,r14d
  1bf638:	rol    r10d,0x13
  1bf63c:	xor    r10d,r8d
  1bf63f:	mov    ebx,r14d
  1bf642:	rol    ebx,0xa
  1bf645:	xor    ebx,r10d
  1bf648:	mov    r10d,r15d
  1bf64b:	and    r10d,r11d
  1bf64e:	mov    esi,r15d
  1bf651:	xor    esi,r11d
  1bf654:	and    esi,r14d
  1bf657:	xor    esi,r10d
  1bf65a:	add    esi,ebx
  1bf65c:	add    esi,edx
  1bf65e:	mov    rbx,rsi
  1bf661:	add    edi,edx
  1bf663:	mov    QWORD PTR [rsp+0x18],r12
  1bf668:	mov    edx,r12d
  1bf66b:	rol    edx,0xf
  1bf66e:	mov    r10d,r12d
  1bf671:	rol    r10d,0xd
  1bf675:	xor    r10d,edx
  1bf678:	mov    esi,r12d
  1bf67b:	shr    esi,0xa
  1bf67e:	xor    esi,r10d
  1bf681:	mov    rdx,QWORD PTR [rsp+0x40]
  1bf686:	add    edx,DWORD PTR [rsp]
  1bf689:	add    esi,edx
  1bf68b:	mov    QWORD PTR [rsp+0xb0],r13
  1bf693:	mov    edx,r13d
  1bf696:	rol    edx,0xf
  1bf699:	mov    r10d,r13d
  1bf69c:	rol    r10d,0xd
  1bf6a0:	xor    r10d,edx
  1bf6a3:	mov    edx,r13d
  1bf6a6:	mov    r8,rdx
  1bf6a9:	shr    r8d,0xa
  1bf6ad:	xor    r8d,r10d
  1bf6b0:	mov    rdx,QWORD PTR [rsp+0x28]
  1bf6b5:	add    edx,DWORD PTR [rsp+0x58]
  1bf6b9:	add    r8d,edx
  1bf6bc:	mov    edx,esi
  1bf6be:	rol    edx,0xf
  1bf6c1:	mov    r10d,esi
  1bf6c4:	rol    r10d,0xd
  1bf6c8:	xor    r10d,edx
  1bf6cb:	mov    r13d,esi
  1bf6ce:	mov    DWORD PTR [rsp+0xa8],esi
  1bf6d5:	shr    r13d,0xa
  1bf6d9:	xor    r13d,r10d
  1bf6dc:	mov    r10,QWORD PTR [rsp+0x80]
  1bf6e4:	add    r10d,DWORD PTR [rsp+0x50]
  1bf6e9:	add    r13d,r10d
  1bf6ec:	mov    QWORD PTR [rsp+0x10],r13
  1bf6f1:	mov    edx,r8d
  1bf6f4:	rol    edx,0xf
  1bf6f7:	mov    r10d,r8d
  1bf6fa:	rol    r10d,0xd
  1bf6fe:	xor    r10d,edx
  1bf701:	mov    edx,r8d
  1bf704:	mov    QWORD PTR [rsp+0x40],r8
  1bf709:	shr    edx,0xa
  1bf70c:	xor    edx,r10d
  1bf70f:	mov    r10d,DWORD PTR [rsp+0xb8]
  1bf717:	add    r10d,ebp
  1bf71a:	add    edx,r10d
  1bf71d:	mov    QWORD PTR [rsp+0x8],rdx
  1bf722:	mov    edx,edi
  1bf724:	rol    edx,0x1a
  1bf727:	mov    r10d,edi
  1bf72a:	rol    r10d,0x15
  1bf72e:	xor    r10d,edx
  1bf731:	mov    edx,edi
  1bf733:	rol    edx,0x7
  1bf736:	xor    edx,r10d
  1bf739:	add    eax,esi
  1bf73b:	mov    r10d,r9d
  1bf73e:	xor    r10d,ecx
  1bf741:	and    r10d,edi
  1bf744:	xor    r10d,ecx
  1bf747:	add    r10d,eax
  1bf74a:	mov    eax,ebx
  1bf74c:	rol    eax,0x1e
  1bf74f:	add    edx,r10d
  1bf752:	add    edx,0xc6e00bf3
  1bf758:	mov    r10d,ebx
  1bf75b:	rol    r10d,0x13
  1bf75f:	xor    r10d,eax
  1bf762:	mov    eax,ebx
  1bf764:	mov    rsi,rbx
  1bf767:	rol    eax,0xa
  1bf76a:	xor    eax,r10d
  1bf76d:	mov    ebx,r14d
  1bf770:	xor    ebx,r15d
  1bf773:	and    ebx,esi
  1bf775:	mov    r12d,r14d
  1bf778:	and    r12d,r15d
  1bf77b:	xor    r12d,ebx
  1bf77e:	add    r12d,eax
  1bf781:	add    r11d,edx
  1bf784:	mov    eax,r11d
  1bf787:	rol    eax,0x1a
  1bf78a:	add    r12d,edx
  1bf78d:	mov    edx,r11d
  1bf790:	rol    edx,0x15
  1bf793:	xor    edx,eax
  1bf795:	mov    eax,r11d
  1bf798:	rol    eax,0x7
  1bf79b:	xor    eax,edx
  1bf79d:	add    ecx,r8d
  1bf7a0:	mov    edx,edi
  1bf7a2:	xor    edx,r9d
  1bf7a5:	and    edx,r11d
  1bf7a8:	xor    edx,r9d
  1bf7ab:	add    edx,ecx
  1bf7ad:	add    eax,edx
  1bf7af:	add    eax,0xd5a79147
  1bf7b4:	mov    ecx,r12d
  1bf7b7:	rol    ecx,0x1e
  1bf7ba:	mov    edx,r12d
  1bf7bd:	rol    edx,0x13
  1bf7c0:	xor    edx,ecx
  1bf7c2:	mov    ecx,r12d
  1bf7c5:	rol    ecx,0xa
  1bf7c8:	xor    ecx,edx
  1bf7ca:	mov    r10,rsi
  1bf7cd:	mov    ebx,r10d
  1bf7d0:	and    ebx,r14d
  1bf7d3:	mov    ebp,r10d
  1bf7d6:	xor    ebp,r14d
  1bf7d9:	and    ebp,r12d
  1bf7dc:	xor    ebp,ebx
  1bf7de:	add    ebp,ecx
  1bf7e0:	add    ebp,eax
  1bf7e2:	add    r15d,eax
  1bf7e5:	mov    eax,r15d
  1bf7e8:	rol    eax,0x1a
  1bf7eb:	mov    ecx,r15d
  1bf7ee:	rol    ecx,0x15
  1bf7f1:	xor    ecx,eax
  1bf7f3:	mov    eax,r15d
  1bf7f6:	rol    eax,0x7
  1bf7f9:	xor    eax,ecx
  1bf7fb:	lea    ecx,[r9+r13*1]
  1bf7ff:	mov    r9d,r11d
  1bf802:	xor    r9d,edi
  1bf805:	and    r9d,r15d
  1bf808:	xor    r9d,edi
  1bf80b:	add    r9d,ecx
  1bf80e:	mov    ecx,ebp
  1bf810:	rol    ecx,0x1e
  1bf813:	add    eax,r9d
  1bf816:	add    eax,0x6ca6351
  1bf81b:	mov    r9d,ebp
  1bf81e:	rol    r9d,0x13
  1bf822:	xor    r9d,ecx
  1bf825:	mov    ecx,ebp
  1bf827:	rol    ecx,0xa
  1bf82a:	xor    ecx,r9d
  1bf82d:	mov    r9d,r12d
  1bf830:	xor    r9d,r10d
  1bf833:	and    r9d,ebp
  1bf836:	mov    edx,r12d
  1bf839:	and    edx,r10d
  1bf83c:	xor    edx,r9d
  1bf83f:	add    edx,ecx
  1bf841:	mov    rsi,rdx
  1bf844:	add    r14d,eax
  1bf847:	mov    ecx,r14d
  1bf84a:	rol    ecx,0x1a
  1bf84d:	add    esi,eax
  1bf84f:	mov    eax,r14d
  1bf852:	rol    eax,0x15
  1bf855:	xor    eax,ecx
  1bf857:	mov    ecx,r14d
  1bf85a:	mov    QWORD PTR [rsp+0x20],r14
  1bf85f:	rol    ecx,0x7
  1bf862:	xor    ecx,eax
  1bf864:	mov    rax,QWORD PTR [rsp+0x8]
  1bf869:	add    eax,edi
  1bf86b:	mov    edi,r15d
  1bf86e:	mov    DWORD PTR [rsp+0x28],r11d
  1bf873:	xor    edi,r11d
  1bf876:	and    edi,r14d
  1bf879:	xor    edi,r11d
  1bf87c:	add    edi,eax
  1bf87e:	lea    edx,[rcx+rdi*1]
  1bf881:	add    edx,0x14292967
  1bf887:	mov    ecx,esi
  1bf889:	rol    ecx,0x1e
  1bf88c:	mov    r9d,esi
  1bf88f:	rol    r9d,0x13
  1bf893:	xor    r9d,ecx
  1bf896:	mov    edi,esi
  1bf898:	mov    rcx,rsi
  1bf89b:	mov    QWORD PTR [rsp+0x70],rsi
  1bf8a0:	rol    edi,0xa
  1bf8a3:	xor    edi,r9d
  1bf8a6:	mov    r9d,ebp
  1bf8a9:	and    r9d,r12d
  1bf8ac:	mov    ebx,DWORD PTR [rsp+0x38]
  1bf8b0:	mov    eax,ebx
  1bf8b2:	rol    eax,0x19
  1bf8b5:	mov    r8,QWORD PTR [rsp+0x60]
  1bf8ba:	mov    r14d,r8d
  1bf8bd:	rol    r14d,0x19
  1bf8c1:	mov    r11d,ebp
  1bf8c4:	xor    r11d,r12d
  1bf8c7:	mov    rsi,QWORD PTR [rsp+0x48]
  1bf8cc:	mov    r13d,esi
  1bf8cf:	rol    r13d,0x19
  1bf8d3:	mov    DWORD PTR [rsp+0x68],r13d
  1bf8d8:	and    r11d,ecx
  1bf8db:	mov    rcx,QWORD PTR [rsp+0x88]
  1bf8e3:	mov    r13d,ecx
  1bf8e6:	rol    r13d,0x19
  1bf8ea:	mov    DWORD PTR [rsp+0xa0],r13d
  1bf8f2:	xor    r11d,r9d
  1bf8f5:	mov    r9d,ebx
  1bf8f8:	rol    r9d,0xe
  1bf8fc:	add    r11d,edi
  1bf8ff:	mov    edi,r8d
  1bf902:	rol    edi,0xe
  1bf905:	add    r11d,edx
  1bf908:	mov    ebx,esi
  1bf90a:	rol    ebx,0xe
  1bf90d:	add    r10d,edx
  1bf910:	mov    QWORD PTR [rsp+0xc0],r10
  1bf918:	mov    edx,ecx
  1bf91a:	rol    edx,0xe
  1bf91d:	mov    esi,edx
  1bf91f:	xor    r9d,eax
  1bf922:	mov    DWORD PTR [rsp+0x80],r9d
  1bf92a:	mov    r13d,DWORD PTR [rsp+0x34]
  1bf92f:	mov    ecx,r13d
  1bf932:	rol    ecx,0x19
  1bf935:	mov    r10d,edi
  1bf938:	xor    r10d,r14d
  1bf93b:	mov    rdi,QWORD PTR [rsp+0x50]
  1bf940:	mov    edx,edi
  1bf942:	rol    edx,0x19
  1bf945:	xor    ebx,DWORD PTR [rsp+0x68]
  1bf949:	mov    r14,QWORD PTR [rsp+0x58]
  1bf94e:	mov    r9d,r14d
  1bf951:	rol    r9d,0x19
  1bf955:	xor    esi,DWORD PTR [rsp+0xa0]
  1bf95c:	mov    DWORD PTR [rsp+0x68],esi
  1bf960:	mov    eax,r13d
  1bf963:	rol    eax,0xe
  1bf966:	xor    eax,ecx
  1bf968:	mov    ecx,edi
  1bf96a:	rol    ecx,0xe
  1bf96d:	xor    ecx,edx
  1bf96f:	mov    edx,r14d
  1bf972:	rol    edx,0xe
  1bf975:	xor    edx,r9d
  1bf978:	mov    r8,QWORD PTR [rsp]
  1bf97c:	mov    r9d,r8d
  1bf97f:	rol    r9d,0x19
  1bf983:	mov    esi,r8d
  1bf986:	rol    esi,0xe
  1bf989:	xor    esi,r9d
  1bf98c:	shr    r13d,0x3
  1bf990:	xor    r13d,eax
  1bf993:	add    r13d,edi
  1bf996:	mov    DWORD PTR [rsp+0xa0],r13d
  1bf99e:	shr    edi,0x3
  1bf9a1:	xor    edi,ecx
  1bf9a3:	mov    rcx,r14
  1bf9a6:	add    edi,ecx
  1bf9a8:	mov    QWORD PTR [rsp+0x50],rdi
  1bf9ad:	shr    ecx,0x3
  1bf9b0:	xor    ecx,edx
  1bf9b2:	mov    rax,r8
  1bf9b5:	add    ecx,eax
  1bf9b7:	mov    QWORD PTR [rsp+0x58],rcx
  1bf9bc:	shr    eax,0x3
  1bf9bf:	xor    eax,esi
  1bf9c1:	mov    r8d,DWORD PTR [rsp+0x38]
  1bf9c6:	add    eax,r8d
  1bf9c9:	mov    QWORD PTR [rsp],rax
  1bf9cd:	shr    r8d,0x3
  1bf9d1:	xor    r8d,DWORD PTR [rsp+0x80]
  1bf9d9:	mov    r13,QWORD PTR [rsp+0x60]
  1bf9de:	add    r8d,r13d
  1bf9e1:	shr    r13d,0x3
  1bf9e5:	xor    r13d,r10d
  1bf9e8:	mov    rcx,QWORD PTR [rsp+0x48]
  1bf9ed:	add    r13d,ecx
  1bf9f0:	shr    ecx,0x3
  1bf9f3:	xor    ecx,ebx
  1bf9f5:	mov    rdx,QWORD PTR [rsp+0x88]
  1bf9fd:	add    ecx,edx
  1bf9ff:	mov    rbx,rcx
  1bfa02:	shr    edx,0x3
  1bfa05:	xor    edx,DWORD PTR [rsp+0x68]
  1bfa09:	mov    rdi,QWORD PTR [rsp+0x10]
  1bfa0e:	mov    ecx,edi
  1bfa10:	rol    ecx,0xf
  1bfa13:	add    edx,DWORD PTR [rsp+0x78]
  1bfa17:	mov    rsi,rdx
  1bfa1a:	mov    edx,edi
  1bfa1c:	rol    edx,0xd
  1bfa1f:	xor    edx,ecx
  1bfa21:	mov    r9d,edi
  1bfa24:	shr    r9d,0xa
  1bfa28:	xor    r9d,edx
  1bfa2b:	add    esi,DWORD PTR [rsp+0x98]
  1bfa32:	mov    rax,QWORD PTR [rsp+0x8]
  1bfa37:	mov    ecx,eax
  1bfa39:	rol    ecx,0xf
  1bfa3c:	add    r9d,esi
  1bfa3f:	mov    edx,eax
  1bfa41:	rol    edx,0xd
  1bfa44:	xor    edx,ecx
  1bfa46:	mov    esi,eax
  1bfa48:	shr    esi,0xa
  1bfa4b:	xor    esi,edx
  1bfa4d:	add    ebx,DWORD PTR [rsp+0x18]
  1bfa51:	mov    ecx,r9d
  1bfa54:	rol    ecx,0xf
  1bfa57:	add    esi,ebx
  1bfa59:	mov    edx,r9d
  1bfa5c:	rol    edx,0xd
  1bfa5f:	xor    edx,ecx
  1bfa61:	mov    ebx,r9d
  1bfa64:	shr    ebx,0xa
  1bfa67:	xor    ebx,edx
  1bfa69:	add    r13d,DWORD PTR [rsp+0xb0]
  1bfa71:	mov    ecx,esi
  1bfa73:	rol    ecx,0xf
  1bfa76:	add    ebx,r13d
  1bfa79:	mov    edx,esi
  1bfa7b:	rol    edx,0xd
  1bfa7e:	xor    edx,ecx
  1bfa80:	mov    edi,esi
  1bfa82:	mov    QWORD PTR [rsp+0x88],rsi
  1bfa8a:	shr    edi,0xa
  1bfa8d:	xor    edi,edx
  1bfa8f:	add    r8d,DWORD PTR [rsp+0xa8]
  1bfa97:	mov    r14,QWORD PTR [rsp+0xc0]
  1bfa9f:	mov    ecx,r14d
  1bfaa2:	rol    ecx,0x1a
  1bfaa5:	add    edi,r8d
  1bfaa8:	mov    eax,r14d
  1bfaab:	rol    eax,0x15
  1bfaae:	xor    eax,ecx
  1bfab0:	mov    ecx,r14d
  1bfab3:	rol    ecx,0x7
  1bfab6:	xor    ecx,eax
  1bfab8:	mov    edx,DWORD PTR [rsp+0x28]
  1bfabc:	add    edx,r9d
  1bfabf:	mov    DWORD PTR [rsp+0x68],r9d
  1bfac4:	mov    r13,QWORD PTR [rsp+0x20]
  1bfac9:	mov    eax,r13d
  1bfacc:	xor    eax,r15d
  1bfacf:	and    eax,r14d
  1bfad2:	xor    eax,r15d
  1bfad5:	add    eax,edx
  1bfad7:	add    eax,ecx
  1bfad9:	add    eax,0x27b70a85
  1bfade:	mov    ecx,r11d
  1bfae1:	rol    ecx,0x1e
  1bfae4:	mov    edx,r11d
  1bfae7:	rol    edx,0x13
  1bfaea:	xor    edx,ecx
  1bfaec:	mov    ecx,r11d
  1bfaef:	rol    ecx,0xa
  1bfaf2:	xor    ecx,edx
  1bfaf4:	mov    r10,QWORD PTR [rsp+0x70]
  1bfaf9:	mov    edx,r10d
  1bfafc:	xor    edx,ebp
  1bfafe:	and    edx,r11d
  1bfb01:	mov    r8d,r10d
  1bfb04:	and    r8d,ebp
  1bfb07:	xor    r8d,edx
  1bfb0a:	add    r8d,ecx
  1bfb0d:	add    r8d,eax
  1bfb10:	add    r12d,eax
  1bfb13:	mov    eax,r12d
  1bfb16:	rol    eax,0x1a
  1bfb19:	mov    ecx,r12d
  1bfb1c:	rol    ecx,0x15
  1bfb1f:	xor    ecx,eax
  1bfb21:	mov    eax,r12d
  1bfb24:	rol    eax,0x7
  1bfb27:	xor    eax,ecx
  1bfb29:	lea    ecx,[rsi+r15*1]
  1bfb2d:	mov    edx,r14d
  1bfb30:	mov    rsi,r13
  1bfb33:	xor    edx,esi
  1bfb35:	and    edx,r12d
  1bfb38:	mov    r15d,r12d
  1bfb3b:	xor    edx,esi
  1bfb3d:	add    edx,ecx
  1bfb3f:	mov    ecx,r8d
  1bfb42:	rol    ecx,0x1e
  1bfb45:	add    eax,edx
  1bfb47:	add    eax,0x2e1b2138
  1bfb4c:	mov    edx,r8d
  1bfb4f:	rol    edx,0x13
  1bfb52:	xor    edx,ecx
  1bfb54:	mov    ecx,r8d
  1bfb57:	rol    ecx,0xa
  1bfb5a:	xor    ecx,edx
  1bfb5c:	mov    edx,r11d
  1bfb5f:	and    edx,r10d
  1bfb62:	mov    r13d,r11d
  1bfb65:	xor    r13d,r10d
  1bfb68:	and    r13d,r8d
  1bfb6b:	xor    r13d,edx
  1bfb6e:	add    r13d,ecx
  1bfb71:	add    ebp,eax
  1bfb73:	mov    ecx,ebp
  1bfb75:	rol    ecx,0x1a
  1bfb78:	add    r13d,eax
  1bfb7b:	mov    eax,ebp
  1bfb7d:	rol    eax,0x15
  1bfb80:	xor    eax,ecx
  1bfb82:	mov    ecx,ebp
  1bfb84:	rol    ecx,0x7
  1bfb87:	xor    ecx,eax
  1bfb89:	mov    edx,r12d
  1bfb8c:	xor    edx,r14d
  1bfb8f:	and    edx,ebp
  1bfb91:	xor    edx,r14d
  1bfb94:	add    edx,ebx
  1bfb96:	add    edx,esi
  1bfb98:	lea    eax,[rcx+rdx*1]
  1bfb9b:	add    eax,0x4d2c6dfc
  1bfba0:	mov    ecx,r13d
  1bfba3:	rol    ecx,0x1e
  1bfba6:	mov    edx,r13d
  1bfba9:	rol    edx,0x13
  1bfbac:	xor    edx,ecx
  1bfbae:	mov    ecx,r13d
  1bfbb1:	rol    ecx,0xa
  1bfbb4:	xor    ecx,edx
  1bfbb6:	mov    edx,r8d
  1bfbb9:	xor    edx,r11d
  1bfbbc:	and    edx,r13d
  1bfbbf:	mov    r12d,r8d
  1bfbc2:	and    r12d,r11d
  1bfbc5:	xor    r12d,edx
  1bfbc8:	add    r12d,ecx
  1bfbcb:	add    r12d,eax
  1bfbce:	mov    rsi,r10
  1bfbd1:	add    esi,eax
  1bfbd3:	mov    eax,esi
  1bfbd5:	rol    eax,0x1a
  1bfbd8:	mov    ecx,esi
  1bfbda:	rol    ecx,0x15
  1bfbdd:	xor    ecx,eax
  1bfbdf:	mov    eax,esi
  1bfbe1:	rol    eax,0x7
  1bfbe4:	xor    eax,ecx
  1bfbe6:	lea    ecx,[rdi+r14*1]
  1bfbea:	mov    edx,ebp
  1bfbec:	xor    edx,r15d
  1bfbef:	and    edx,esi
  1bfbf1:	mov    r10,rsi
  1bfbf4:	xor    edx,r15d
  1bfbf7:	add    edx,ecx
  1bfbf9:	mov    ecx,r12d
  1bfbfc:	rol    ecx,0x1e
  1bfbff:	add    eax,edx
  1bfc01:	add    eax,0x53380d13
  1bfc06:	mov    edx,r12d
  1bfc09:	rol    edx,0x13
  1bfc0c:	xor    edx,ecx
  1bfc0e:	mov    ecx,r12d
  1bfc11:	rol    ecx,0xa
  1bfc14:	xor    ecx,edx
  1bfc16:	mov    edx,r13d
  1bfc19:	and    edx,r8d
  1bfc1c:	mov    esi,r13d
  1bfc1f:	xor    esi,r8d
  1bfc22:	and    esi,r12d
  1bfc25:	xor    esi,edx
  1bfc27:	add    esi,ecx
  1bfc29:	add    esi,eax
  1bfc2b:	mov    r14,rsi
  1bfc2e:	mov    QWORD PTR [rsp+0x80],rbx
  1bfc36:	mov    ecx,ebx
  1bfc38:	rol    ecx,0xf
  1bfc3b:	add    r11d,eax
  1bfc3e:	mov    eax,ebx
  1bfc40:	rol    eax,0xd
  1bfc43:	xor    eax,ecx
  1bfc45:	mov    edx,ebx
  1bfc47:	shr    edx,0xa
  1bfc4a:	xor    edx,eax
  1bfc4c:	mov    rcx,QWORD PTR [rsp]
  1bfc50:	add    ecx,DWORD PTR [rsp+0x40]
  1bfc54:	mov    QWORD PTR [rsp+0x38],rdi
  1bfc59:	mov    eax,edi
  1bfc5b:	rol    eax,0xf
  1bfc5e:	add    edx,ecx
  1bfc60:	mov    ecx,edi
  1bfc62:	rol    ecx,0xd
  1bfc65:	xor    ecx,eax
  1bfc67:	mov    esi,edi
  1bfc69:	shr    esi,0xa
  1bfc6c:	xor    esi,ecx
  1bfc6e:	mov    rcx,QWORD PTR [rsp+0x58]
  1bfc73:	add    ecx,DWORD PTR [rsp+0x10]
  1bfc77:	mov    eax,edx
  1bfc79:	rol    eax,0xf
  1bfc7c:	add    esi,ecx
  1bfc7e:	mov    ecx,edx
  1bfc80:	rol    ecx,0xd
  1bfc83:	xor    ecx,eax
  1bfc85:	mov    edi,edx
  1bfc87:	mov    DWORD PTR [rsp+0x78],edx
  1bfc8b:	shr    edi,0xa
  1bfc8e:	xor    edi,ecx
  1bfc90:	mov    rcx,QWORD PTR [rsp+0x50]
  1bfc95:	add    ecx,DWORD PTR [rsp+0x8]
  1bfc99:	mov    eax,esi
  1bfc9b:	rol    eax,0xf
  1bfc9e:	add    edi,ecx
  1bfca0:	mov    QWORD PTR [rsp],rdi
  1bfca4:	mov    ecx,esi
  1bfca6:	rol    ecx,0xd
  1bfca9:	xor    ecx,eax
  1bfcab:	mov    eax,esi
  1bfcad:	mov    rbx,rsi
  1bfcb0:	mov    QWORD PTR [rsp+0x48],rsi
  1bfcb5:	shr    eax,0xa
  1bfcb8:	xor    eax,ecx
  1bfcba:	mov    rcx,rax
  1bfcbd:	mov    esi,DWORD PTR [rsp+0xa0]
  1bfcc4:	add    esi,r9d
  1bfcc7:	mov    eax,r11d
  1bfcca:	rol    eax,0x1a
  1bfccd:	add    ecx,esi
  1bfccf:	mov    QWORD PTR [rsp+0x20],rcx
  1bfcd4:	mov    ecx,r11d
  1bfcd7:	rol    ecx,0x15
  1bfcda:	xor    ecx,eax
  1bfcdc:	mov    eax,r11d
  1bfcdf:	rol    eax,0x7
  1bfce2:	xor    eax,ecx
  1bfce4:	add    r15d,edx
  1bfce7:	mov    ecx,r10d
  1bfcea:	xor    ecx,ebp
  1bfcec:	and    ecx,r11d
  1bfcef:	xor    ecx,ebp
  1bfcf1:	add    ecx,r15d
  1bfcf4:	add    ecx,eax
  1bfcf6:	add    ecx,0x650a7354
  1bfcfc:	mov    r15,r14
  1bfcff:	mov    eax,r15d
  1bfd02:	rol    eax,0x1e
  1bfd05:	mov    edx,r15d
  1bfd08:	rol    edx,0x13
  1bfd0b:	xor    edx,eax
  1bfd0d:	mov    r9d,r15d
  1bfd10:	rol    r9d,0xa
  1bfd14:	xor    r9d,edx
  1bfd17:	mov    edx,r12d
  1bfd1a:	xor    edx,r13d
  1bfd1d:	and    edx,r15d
  1bfd20:	mov    eax,r12d
  1bfd23:	and    eax,r13d
  1bfd26:	xor    eax,edx
  1bfd28:	add    eax,r9d
  1bfd2b:	add    eax,ecx
  1bfd2d:	mov    esi,r8d
  1bfd30:	add    esi,ecx
  1bfd32:	mov    ecx,esi
  1bfd34:	rol    ecx,0x1a
  1bfd37:	mov    edx,esi
  1bfd39:	rol    edx,0x15
  1bfd3c:	xor    edx,ecx
  1bfd3e:	mov    ecx,esi
  1bfd40:	rol    ecx,0x7
  1bfd43:	xor    ecx,edx
  1bfd45:	lea    edx,[rbx+rbp*1]
  1bfd48:	mov    r9d,r11d
  1bfd4b:	xor    r9d,r10d
  1bfd4e:	and    r9d,esi
  1bfd51:	xor    r9d,r10d
  1bfd54:	mov    r8,r10
  1bfd57:	add    r9d,edx
  1bfd5a:	mov    edx,eax
  1bfd5c:	rol    edx,0x1e
  1bfd5f:	add    ecx,r9d
  1bfd62:	add    ecx,0x766a0abb
  1bfd68:	mov    r9d,eax
  1bfd6b:	rol    r9d,0x13
  1bfd6f:	xor    r9d,edx
  1bfd72:	mov    edx,eax
  1bfd74:	mov    ebp,eax
  1bfd76:	rol    edx,0xa
  1bfd79:	xor    edx,r9d
  1bfd7c:	mov    r10d,r15d
  1bfd7f:	and    r10d,r12d
  1bfd82:	mov    eax,r15d
  1bfd85:	xor    eax,r12d
  1bfd88:	and    eax,ebp
  1bfd8a:	xor    eax,r10d
  1bfd8d:	add    eax,edx
  1bfd8f:	mov    rbx,rax
  1bfd92:	add    r13d,ecx
  1bfd95:	mov    edx,r13d
  1bfd98:	rol    edx,0x1a
  1bfd9b:	add    ebx,ecx
  1bfd9d:	mov    ecx,r13d
  1bfda0:	rol    ecx,0x15
  1bfda3:	xor    ecx,edx
  1bfda5:	mov    edx,r13d
  1bfda8:	rol    edx,0x7
  1bfdab:	xor    edx,ecx
  1bfdad:	mov    r10d,esi
  1bfdb0:	xor    r10d,r11d
  1bfdb3:	and    r10d,r13d
  1bfdb6:	xor    r10d,r11d
  1bfdb9:	add    r10d,edi
  1bfdbc:	add    r10d,r8d
  1bfdbf:	lea    ecx,[rdx+r10*1]
  1bfdc3:	add    ecx,0x81c2c92e
  1bfdc9:	mov    edx,ebx
  1bfdcb:	rol    edx,0x1e
  1bfdce:	mov    r10d,ebx
  1bfdd1:	rol    r10d,0x13
  1bfdd5:	xor    r10d,edx
  1bfdd8:	mov    edx,ebx
  1bfdda:	rol    edx,0xa
  1bfddd:	xor    edx,r10d
  1bfde0:	mov    r10d,ebp
  1bfde3:	mov    QWORD PTR [rsp+0x70],r14
  1bfde8:	xor    r10d,r15d
  1bfdeb:	and    r10d,ebx
  1bfdee:	mov    eax,ebp
  1bfdf0:	and    eax,r15d
  1bfdf3:	xor    eax,r10d
  1bfdf6:	add    eax,edx
  1bfdf8:	add    eax,ecx
  1bfdfa:	mov    rdi,rax
  1bfdfd:	add    r12d,ecx
  1bfe00:	mov    ecx,r12d
  1bfe03:	rol    ecx,0x1a
  1bfe06:	mov    edx,r12d
  1bfe09:	rol    edx,0x15
  1bfe0c:	xor    edx,ecx
  1bfe0e:	mov    ecx,r12d
  1bfe11:	mov    QWORD PTR [rsp+0x50],r12
  1bfe16:	rol    ecx,0x7
  1bfe19:	xor    ecx,edx
  1bfe1b:	mov    rax,QWORD PTR [rsp+0x20]
  1bfe20:	lea    edx,[rax+r11*1]
  1bfe24:	mov    r8d,r13d
  1bfe27:	mov    DWORD PTR [rsp+0xc0],esi
  1bfe2e:	xor    r8d,esi
  1bfe31:	and    r8d,r12d
  1bfe34:	xor    r8d,esi
  1bfe37:	add    r8d,edx
  1bfe3a:	mov    edx,edi
  1bfe3c:	rol    edx,0x1e
  1bfe3f:	lea    r9d,[rcx+r8*1]
  1bfe43:	add    r9d,0x92722c85
  1bfe4a:	mov    ecx,edi
  1bfe4c:	rol    ecx,0x13
  1bfe4f:	xor    ecx,edx
  1bfe51:	mov    r14d,edi
  1bfe54:	mov    QWORD PTR [rsp+0xc8],rdi
  1bfe5c:	rol    r14d,0xa
  1bfe60:	xor    r14d,ecx
  1bfe63:	mov    esi,DWORD PTR [rsp+0xa8]
  1bfe6a:	mov    r10d,esi
  1bfe6d:	rol    r10d,0x19
  1bfe71:	mov    rdx,QWORD PTR [rsp+0xb0]
  1bfe79:	mov    eax,edx
  1bfe7b:	rol    eax,0x19
  1bfe7e:	mov    DWORD PTR [rsp+0x28],eax
  1bfe82:	mov    r15,rbx
  1bfe85:	mov    QWORD PTR [rsp+0xb8],rbx
  1bfe8d:	mov    r11d,r15d
  1bfe90:	mov    DWORD PTR [rsp+0xa0],ebp
  1bfe97:	and    r11d,ebp
  1bfe9a:	mov    rcx,QWORD PTR [rsp+0x18]
  1bfe9f:	mov    r12d,ecx
  1bfea2:	rol    r12d,0x19
  1bfea6:	mov    rax,QWORD PTR [rsp+0x98]
  1bfeae:	mov    r8d,eax
  1bfeb1:	rol    r8d,0x19
  1bfeb5:	mov    DWORD PTR [rsp+0x60],r8d
  1bfeba:	xor    r15d,ebp
  1bfebd:	mov    r8d,esi
  1bfec0:	rol    r8d,0xe
  1bfec4:	mov    ebx,r8d
  1bfec7:	and    r15d,edi
  1bfeca:	mov    esi,edx
  1bfecc:	rol    esi,0xe
  1bfecf:	xor    r15d,r11d
  1bfed2:	mov    r8d,ecx
  1bfed5:	rol    r8d,0xe
  1bfed9:	add    r15d,r14d
  1bfedc:	rol    eax,0xe
  1bfedf:	mov    DWORD PTR [rsp+0x58],eax
  1bfee3:	add    r15d,r9d
  1bfee6:	mov    QWORD PTR [rsp+0xf0],r15
  1bfeee:	mov    eax,DWORD PTR [rsp+0x68]
  1bfef2:	mov    ecx,eax
  1bfef4:	rol    ecx,0x19
  1bfef7:	mov    rdi,QWORD PTR [rsp+0x70]
  1bfefc:	add    edi,r9d
  1bfeff:	mov    QWORD PTR [rsp+0x70],rdi
  1bff04:	mov    r9,QWORD PTR [rsp+0x8]
  1bff09:	mov    edx,r9d
  1bff0c:	rol    edx,0x19
  1bff0f:	mov    r11d,ebx
  1bff12:	xor    r11d,r10d
  1bff15:	mov    rbp,QWORD PTR [rsp+0x10]
  1bff1a:	mov    r10d,ebp
  1bff1d:	rol    r10d,0x19
  1bff21:	mov    ebx,esi
  1bff23:	xor    ebx,DWORD PTR [rsp+0x28]
  1bff27:	mov    rdi,QWORD PTR [rsp+0x40]
  1bff2c:	mov    esi,edi
  1bff2e:	rol    esi,0x19
  1bff31:	mov    r14d,r8d
  1bff34:	xor    r14d,r12d
  1bff37:	mov    r12d,eax
  1bff3a:	mov    r8d,eax
  1bff3d:	rol    r12d,0xe
  1bff41:	mov    r15d,DWORD PTR [rsp+0x58]
  1bff46:	xor    r15d,DWORD PTR [rsp+0x60]
  1bff4b:	mov    eax,r9d
  1bff4e:	rol    eax,0xe
  1bff51:	xor    r12d,ecx
  1bff54:	mov    ecx,ebp
  1bff56:	rol    ecx,0xe
  1bff59:	xor    eax,edx
  1bff5b:	mov    edx,edi
  1bff5d:	rol    edx,0xe
  1bff60:	xor    ecx,r10d
  1bff63:	xor    edx,esi
  1bff65:	mov    esi,r8d
  1bff68:	shr    esi,0x3
  1bff6b:	xor    esi,r12d
  1bff6e:	add    esi,r9d
  1bff71:	shr    r9d,0x3
  1bff75:	xor    r9d,eax
  1bff78:	mov    rax,rbp
  1bff7b:	add    r9d,eax
  1bff7e:	mov    QWORD PTR [rsp+0x8],r9
  1bff83:	shr    eax,0x3
  1bff86:	xor    eax,ecx
  1bff88:	add    eax,edi
  1bff8a:	mov    QWORD PTR [rsp+0x10],rax
  1bff8f:	shr    edi,0x3
  1bff92:	xor    edi,edx
  1bff94:	mov    r10d,DWORD PTR [rsp+0xa8]
  1bff9c:	add    edi,r10d
  1bff9f:	mov    QWORD PTR [rsp+0x40],rdi
  1bffa4:	shr    r10d,0x3
  1bffa8:	xor    r10d,r11d
  1bffab:	mov    r12,QWORD PTR [rsp+0xb0]
  1bffb3:	add    r10d,r12d
  1bffb6:	shr    r12d,0x3
  1bffba:	xor    r12d,ebx
  1bffbd:	mov    rax,QWORD PTR [rsp+0x18]
  1bffc2:	add    r12d,eax
  1bffc5:	shr    eax,0x3
  1bffc8:	xor    eax,r14d
  1bffcb:	mov    rcx,QWORD PTR [rsp+0x98]
  1bffd3:	add    eax,ecx
  1bffd5:	mov    r11,rax
  1bffd8:	shr    ecx,0x3
  1bffdb:	xor    ecx,r15d
  1bffde:	add    ecx,DWORD PTR [rsp+0x34]
  1bffe2:	mov    r8,rcx
  1bffe5:	mov    rdx,QWORD PTR [rsp]
  1bffe9:	mov    eax,edx
  1bffeb:	rol    eax,0xf
  1bffee:	mov    ecx,edx
  1bfff0:	rol    ecx,0xd
  1bfff3:	xor    ecx,eax
  1bfff5:	shr    edx,0xa
  1bfff8:	xor    edx,ecx
  1bfffa:	add    r8d,DWORD PTR [rsp+0x88]
  1c0002:	add    edx,r8d
  1c0005:	mov    r8,QWORD PTR [rsp+0x20]
  1c000a:	mov    eax,r8d
  1c000d:	rol    eax,0xf
  1c0010:	mov    ecx,r8d
  1c0013:	rol    ecx,0xd
  1c0016:	xor    ecx,eax
  1c0018:	shr    r8d,0xa
  1c001c:	xor    r8d,ecx
  1c001f:	add    r11d,DWORD PTR [rsp+0x80]
  1c0027:	add    r8d,r11d
  1c002a:	mov    eax,edx
  1c002c:	rol    eax,0xf
  1c002f:	mov    ecx,edx
  1c0031:	rol    ecx,0xd
  1c0034:	xor    ecx,eax
  1c0036:	mov    eax,edx
  1c0038:	mov    DWORD PTR [rsp+0x58],edx
  1c003c:	shr    eax,0xa
  1c003f:	xor    eax,ecx
  1c0041:	add    r12d,DWORD PTR [rsp+0x38]
  1c0046:	add    eax,r12d
  1c0049:	mov    r14,rax
  1c004c:	mov    eax,r8d
  1c004f:	rol    eax,0xf
  1c0052:	mov    ecx,r8d
  1c0055:	rol    ecx,0xd
  1c0058:	xor    ecx,eax
  1c005a:	mov    eax,r8d
  1c005d:	mov    r11,r8
  1c0060:	mov    QWORD PTR [rsp+0x60],r8
  1c0065:	shr    eax,0xa
  1c0068:	xor    eax,ecx
  1c006a:	add    r10d,DWORD PTR [rsp+0x78]
  1c006f:	add    eax,r10d
  1c0072:	mov    r8,rax
  1c0075:	mov    rbp,QWORD PTR [rsp+0x70]
  1c007a:	mov    eax,ebp
  1c007c:	rol    eax,0x1a
  1c007f:	mov    ecx,ebp
  1c0081:	rol    ecx,0x15
  1c0084:	xor    ecx,eax
  1c0086:	mov    eax,ebp
  1c0088:	rol    eax,0x7
  1c008b:	xor    eax,ecx
  1c008d:	mov    edi,DWORD PTR [rsp+0xc0]
  1c0094:	add    edi,edx
  1c0096:	mov    r10,QWORD PTR [rsp+0x50]
  1c009b:	mov    ecx,r10d
  1c009e:	xor    ecx,r13d
  1c00a1:	and    ecx,ebp
  1c00a3:	xor    ecx,r13d
  1c00a6:	add    ecx,edi
  1c00a8:	mov    r15,QWORD PTR [rsp+0xf0]
  1c00b0:	mov    edx,r15d
  1c00b3:	rol    edx,0x1e
  1c00b6:	add    eax,ecx
  1c00b8:	add    eax,0xa2bfe8a1
  1c00bd:	mov    ecx,r15d
  1c00c0:	rol    ecx,0x13
  1c00c3:	xor    ecx,edx
  1c00c5:	mov    edx,r15d
  1c00c8:	rol    edx,0xa
  1c00cb:	xor    edx,ecx
  1c00cd:	mov    r12,QWORD PTR [rsp+0xc8]
  1c00d5:	mov    ecx,r12d
  1c00d8:	mov    rbx,QWORD PTR [rsp+0xb8]
  1c00e0:	xor    ecx,ebx
  1c00e2:	and    ecx,r15d
  1c00e5:	mov    edi,r12d
  1c00e8:	and    edi,ebx
  1c00ea:	xor    edi,ecx
  1c00ec:	add    edi,edx
  1c00ee:	mov    r9d,DWORD PTR [rsp+0xa0]
  1c00f6:	add    r9d,eax
  1c00f9:	mov    ecx,r9d
  1c00fc:	rol    ecx,0x1a
  1c00ff:	add    edi,eax
  1c0101:	mov    eax,r9d
  1c0104:	rol    eax,0x15
  1c0107:	xor    eax,ecx
  1c0109:	mov    ecx,r9d
  1c010c:	rol    ecx,0x7
  1c010f:	xor    ecx,eax
  1c0111:	mov    edx,ebp
  1c0113:	xor    edx,r10d
  1c0116:	and    edx,r9d
  1c0119:	xor    edx,r10d
  1c011c:	add    edx,r11d
  1c011f:	add    edx,r13d
  1c0122:	lea    eax,[rcx+rdx*1]
  1c0125:	add    eax,0xa81a664b
  1c012a:	mov    ecx,edi
  1c012c:	rol    ecx,0x1e
  1c012f:	mov    edx,edi
  1c0131:	rol    edx,0x13
  1c0134:	xor    edx,ecx
  1c0136:	mov    ecx,edi
  1c0138:	rol    ecx,0xa
  1c013b:	xor    ecx,edx
  1c013d:	mov    edx,r15d
  1c0140:	and    edx,r12d
  1c0143:	mov    r11d,r15d
  1c0146:	xor    r11d,r12d
  1c0149:	and    r11d,edi
  1c014c:	xor    r11d,edx
  1c014f:	add    r11d,ecx
  1c0152:	add    r11d,eax
  1c0155:	add    ebx,eax
  1c0157:	mov    eax,ebx
  1c0159:	rol    eax,0x1a
  1c015c:	mov    ecx,ebx
  1c015e:	rol    ecx,0x15
  1c0161:	xor    ecx,eax
  1c0163:	mov    eax,ebx
  1c0165:	rol    eax,0x7
  1c0168:	xor    eax,ecx
  1c016a:	mov    edx,r9d
  1c016d:	xor    edx,ebp
  1c016f:	and    edx,ebx
  1c0171:	xor    edx,ebp
  1c0173:	add    edx,r14d
  1c0176:	add    edx,r10d
  1c0179:	mov    ecx,r11d
  1c017c:	rol    ecx,0x1e
  1c017f:	add    eax,edx
  1c0181:	add    eax,0xc24b8b70
  1c0186:	mov    edx,r11d
  1c0189:	rol    edx,0x13
  1c018c:	xor    edx,ecx
  1c018e:	mov    ecx,r11d
  1c0191:	rol    ecx,0xa
  1c0194:	xor    ecx,edx
  1c0196:	mov    edx,edi
  1c0198:	xor    edx,r15d
  1c019b:	and    edx,r11d
  1c019e:	mov    r10d,edi
  1c01a1:	and    r10d,r15d
  1c01a4:	xor    r10d,edx
  1c01a7:	add    r10d,ecx
  1c01aa:	mov    r13,r12
  1c01ad:	add    r13d,eax
  1c01b0:	mov    ecx,r13d
  1c01b3:	rol    ecx,0x1a
  1c01b6:	add    r10d,eax
  1c01b9:	mov    r12,r10
  1c01bc:	mov    eax,r13d
  1c01bf:	rol    eax,0x15
  1c01c2:	xor    eax,ecx
  1c01c4:	mov    ecx,r13d
  1c01c7:	rol    ecx,0x7
  1c01ca:	xor    ecx,eax
  1c01cc:	mov    edx,ebx
  1c01ce:	xor    edx,r9d
  1c01d1:	and    edx,r13d
  1c01d4:	xor    edx,r9d
  1c01d7:	add    edx,r8d
  1c01da:	add    edx,ebp
  1c01dc:	lea    eax,[rcx+rdx*1]
  1c01df:	add    eax,0xc76c51a3
  1c01e4:	mov    ecx,r12d
  1c01e7:	rol    ecx,0x1e
  1c01ea:	mov    edx,r12d
  1c01ed:	rol    edx,0x13
  1c01f0:	xor    edx,ecx
  1c01f2:	mov    ecx,r12d
  1c01f5:	rol    ecx,0xa
  1c01f8:	xor    ecx,edx
  1c01fa:	mov    edx,r11d
  1c01fd:	and    edx,edi
  1c01ff:	mov    r10d,r11d
  1c0202:	xor    r10d,edi
  1c0205:	and    r10d,r12d
  1c0208:	xor    r10d,edx
  1c020b:	add    r10d,ecx
  1c020e:	add    r10d,eax
  1c0211:	add    r15d,eax
  1c0214:	mov    QWORD PTR [rsp+0x28],r14
  1c0219:	mov    eax,r14d
  1c021c:	rol    eax,0xf
  1c021f:	mov    ecx,r14d
  1c0222:	rol    ecx,0xd
  1c0225:	xor    ecx,eax
  1c0227:	mov    edx,r14d
  1c022a:	shr    edx,0xa
  1c022d:	xor    edx,ecx
  1c022f:	mov    rax,QWORD PTR [rsp+0x40]
  1c0234:	add    eax,DWORD PTR [rsp+0x48]
  1c0238:	add    edx,eax
  1c023a:	mov    QWORD PTR [rsp+0x18],r8
  1c023f:	mov    eax,r8d
  1c0242:	rol    eax,0xf
  1c0245:	mov    ecx,r8d
  1c0248:	rol    ecx,0xd
  1c024b:	xor    ecx,eax
  1c024d:	mov    r14d,r8d
  1c0250:	shr    r14d,0xa
  1c0254:	xor    r14d,ecx
  1c0257:	mov    rax,QWORD PTR [rsp+0x10]
  1c025c:	add    eax,DWORD PTR [rsp]
  1c025f:	add    r14d,eax
  1c0262:	mov    eax,edx
  1c0264:	rol    eax,0xf
  1c0267:	mov    ecx,edx
  1c0269:	rol    ecx,0xd
  1c026c:	xor    ecx,eax
  1c026e:	mov    eax,edx
  1c0270:	mov    DWORD PTR [rsp+0xb0],edx
  1c0277:	shr    eax,0xa
  1c027a:	xor    eax,ecx
  1c027c:	mov    rcx,QWORD PTR [rsp+0x8]
  1c0281:	add    ecx,DWORD PTR [rsp+0x20]
  1c0285:	add    eax,ecx
  1c0287:	mov    rbp,rax
  1c028a:	mov    QWORD PTR [rsp+0xa8],rax
  1c0292:	mov    eax,r14d
  1c0295:	rol    eax,0xf
  1c0298:	mov    ecx,r14d
  1c029b:	rol    ecx,0xd
  1c029e:	xor    ecx,eax
  1c02a0:	mov    eax,r14d
  1c02a3:	mov    QWORD PTR [rsp+0x10],r14
  1c02a8:	shr    eax,0xa
  1c02ab:	xor    eax,ecx
  1c02ad:	add    esi,DWORD PTR [rsp+0x58]
  1c02b1:	add    eax,esi
  1c02b3:	mov    QWORD PTR [rsp+0x40],rax
  1c02b8:	mov    eax,r15d
  1c02bb:	rol    eax,0x1a
  1c02be:	mov    ecx,r15d
  1c02c1:	rol    ecx,0x15
  1c02c4:	xor    ecx,eax
  1c02c6:	mov    eax,r15d
  1c02c9:	rol    eax,0x7
  1c02cc:	xor    eax,ecx
  1c02ce:	add    r9d,edx
  1c02d1:	mov    ecx,r13d
  1c02d4:	xor    ecx,ebx
  1c02d6:	and    ecx,r15d
  1c02d9:	xor    ecx,ebx
  1c02db:	add    ecx,r9d
  1c02de:	mov    edx,r10d
  1c02e1:	rol    edx,0x1e
  1c02e4:	add    eax,ecx
  1c02e6:	add    eax,0xd192e819
  1c02eb:	mov    ecx,r10d
  1c02ee:	rol    ecx,0x13
  1c02f1:	xor    ecx,edx
  1c02f3:	mov    edx,r10d
  1c02f6:	rol    edx,0xa
  1c02f9:	xor    edx,ecx
  1c02fb:	mov    ecx,r12d
  1c02fe:	xor    ecx,r11d
  1c0301:	and    ecx,r10d
  1c0304:	mov    esi,r12d
  1c0307:	and    esi,r11d
  1c030a:	xor    esi,ecx
  1c030c:	add    esi,edx
  1c030e:	add    edi,eax
  1c0310:	mov    ecx,edi
  1c0312:	rol    ecx,0x1a
  1c0315:	add    esi,eax
  1c0317:	mov    eax,edi
  1c0319:	rol    eax,0x15
  1c031c:	xor    eax,ecx
  1c031e:	mov    ecx,edi
  1c0320:	mov    r9d,edi
  1c0323:	rol    ecx,0x7
  1c0326:	xor    ecx,eax
  1c0328:	mov    edx,r15d
  1c032b:	xor    edx,r13d
  1c032e:	and    edx,edi
  1c0330:	xor    edx,r13d
  1c0333:	add    edx,r14d
  1c0336:	add    edx,ebx
  1c0338:	lea    eax,[rcx+rdx*1]
  1c033b:	add    eax,0xd6990624
  1c0340:	mov    ecx,esi
  1c0342:	rol    ecx,0x1e
  1c0345:	mov    edx,esi
  1c0347:	rol    edx,0x13
  1c034a:	xor    edx,ecx
  1c034c:	mov    ecx,esi
  1c034e:	rol    ecx,0xa
  1c0351:	xor    ecx,edx
  1c0353:	mov    edx,r10d
  1c0356:	and    edx,r12d
  1c0359:	mov    r8d,r10d
  1c035c:	xor    r8d,r12d
  1c035f:	and    r8d,esi
  1c0362:	mov    edi,esi
  1c0364:	xor    r8d,edx
  1c0367:	add    r8d,ecx
  1c036a:	add    r8d,eax
  1c036d:	add    r11d,eax
  1c0370:	mov    eax,r11d
  1c0373:	rol    eax,0x1a
  1c0376:	mov    ecx,r11d
  1c0379:	rol    ecx,0x15
  1c037c:	xor    ecx,eax
  1c037e:	mov    eax,r11d
  1c0381:	rol    eax,0x7
  1c0384:	xor    eax,ecx
  1c0386:	mov    edx,r9d
  1c0389:	xor    edx,r15d
  1c038c:	and    edx,r11d
  1c038f:	xor    edx,r15d
  1c0392:	add    edx,ebp
  1c0394:	add    edx,r13d
  1c0397:	mov    ecx,r8d
  1c039a:	rol    ecx,0x1e
  1c039d:	add    eax,edx
  1c039f:	add    eax,0xf40e3585
  1c03a4:	mov    edx,r8d
  1c03a7:	rol    edx,0x13
  1c03aa:	xor    edx,ecx
  1c03ac:	mov    ecx,r8d
  1c03af:	rol    ecx,0xa
  1c03b2:	xor    ecx,edx
  1c03b4:	mov    edx,esi
  1c03b6:	xor    edx,r10d
  1c03b9:	and    edx,r8d
  1c03bc:	and    esi,r10d
  1c03bf:	xor    esi,edx
  1c03c1:	add    esi,ecx
  1c03c3:	add    r12d,eax
  1c03c6:	mov    ecx,r12d
  1c03c9:	rol    ecx,0x1a
  1c03cc:	add    esi,eax
  1c03ce:	mov    eax,r12d
  1c03d1:	rol    eax,0x15
  1c03d4:	xor    eax,ecx
  1c03d6:	mov    ecx,r12d
  1c03d9:	mov    QWORD PTR [rsp+0x70],r12
  1c03de:	rol    ecx,0x7
  1c03e1:	xor    ecx,eax
  1c03e3:	mov    rax,QWORD PTR [rsp+0x40]
  1c03e8:	add    eax,r15d
  1c03eb:	mov    edx,r11d
  1c03ee:	mov    DWORD PTR [rsp+0x8],r9d
  1c03f3:	xor    edx,r9d
  1c03f6:	and    edx,r12d
  1c03f9:	xor    edx,r9d
  1c03fc:	add    edx,eax
  1c03fe:	lea    ebx,[rcx+rdx*1]
  1c0401:	add    ebx,0x106aa070
  1c0407:	mov    eax,esi
  1c0409:	rol    eax,0x1e
  1c040c:	mov    ecx,esi
  1c040e:	rol    ecx,0x13
  1c0411:	xor    ecx,eax
  1c0413:	mov    edx,esi
  1c0415:	mov    QWORD PTR [rsp+0xc0],rsi
  1c041d:	rol    edx,0xa
  1c0420:	xor    edx,ecx
  1c0422:	mov    r15,r8
  1c0425:	mov    QWORD PTR [rsp+0xc8],r8
  1c042d:	mov    eax,r15d
  1c0430:	mov    DWORD PTR [rsp+0x34],edi
  1c0434:	and    eax,edi
  1c0436:	mov    r8d,DWORD PTR [rsp+0x78]
  1c043b:	mov    r9d,r8d
  1c043e:	rol    r9d,0x19
  1c0442:	mov    r12,QWORD PTR [rsp+0x38]
  1c0447:	mov    r13d,r12d
  1c044a:	rol    r13d,0x19
  1c044e:	xor    r15d,edi
  1c0451:	mov    rdi,QWORD PTR [rsp+0x80]
  1c0459:	mov    r14d,edi
  1c045c:	rol    r14d,0x19
  1c0460:	and    r15d,esi
  1c0463:	mov    rsi,QWORD PTR [rsp+0x88]
  1c046b:	mov    ecx,esi
  1c046d:	rol    ecx,0x19
  1c0470:	xor    r15d,eax
  1c0473:	mov    eax,r8d
  1c0476:	rol    eax,0xe
  1c0479:	add    r15d,edx
  1c047c:	rol    r12d,0xe
  1c0480:	add    r15d,ebx
  1c0483:	mov    QWORD PTR [rsp+0xa0],r15
  1c048b:	mov    ebp,edi
  1c048d:	rol    ebp,0xe
  1c0490:	add    r10d,ebx
  1c0493:	mov    ebx,esi
  1c0495:	rol    ebx,0xe
  1c0498:	xor    eax,r9d
  1c049b:	mov    edi,eax
  1c049d:	mov    esi,DWORD PTR [rsp+0x58]
  1c04a1:	mov    r9d,esi
  1c04a4:	rol    r9d,0x19
  1c04a8:	xor    r12d,r13d
  1c04ab:	mov    rdx,QWORD PTR [rsp+0x20]
  1c04b0:	mov    r15d,edx
  1c04b3:	rol    r15d,0x19
  1c04b7:	xor    ebp,r14d
  1c04ba:	mov    r8,QWORD PTR [rsp]
  1c04be:	mov    r14d,r8d
  1c04c1:	rol    r14d,0x19
  1c04c5:	xor    ebx,ecx
  1c04c7:	mov    ecx,esi
  1c04c9:	rol    ecx,0xe
  1c04cc:	xor    ecx,r9d
  1c04cf:	mov    r9d,edx
  1c04d2:	rol    r9d,0xe
  1c04d6:	xor    r9d,r15d
  1c04d9:	mov    r15d,r8d
  1c04dc:	rol    r15d,0xe
  1c04e0:	xor    r15d,r14d
  1c04e3:	mov    rax,QWORD PTR [rsp+0x48]
  1c04e8:	mov    r14d,eax
  1c04eb:	rol    r14d,0x19
  1c04ef:	mov    r13d,eax
  1c04f2:	rol    r13d,0xe
  1c04f6:	xor    r13d,r14d
  1c04f9:	mov    r14d,esi
  1c04fc:	shr    r14d,0x3
  1c0500:	xor    r14d,ecx
  1c0503:	add    r14d,edx
  1c0506:	mov    DWORD PTR [rsp+0x98],r14d
  1c050e:	shr    edx,0x3
  1c0511:	xor    edx,r9d
  1c0514:	mov    rcx,r8
  1c0517:	add    edx,ecx
  1c0519:	mov    QWORD PTR [rsp+0x20],rdx
  1c051e:	shr    ecx,0x3
  1c0521:	xor    ecx,r15d
  1c0524:	add    ecx,eax
  1c0526:	mov    QWORD PTR [rsp],rcx
  1c052a:	shr    eax,0x3
  1c052d:	xor    eax,r13d
  1c0530:	mov    ecx,DWORD PTR [rsp+0x78]
  1c0534:	add    eax,ecx
  1c0536:	mov    QWORD PTR [rsp+0x48],rax
  1c053b:	shr    ecx,0x3
  1c053e:	xor    ecx,edi
  1c0540:	mov    r9,QWORD PTR [rsp+0x38]
  1c0545:	add    ecx,r9d
  1c0548:	shr    r9d,0x3
  1c054c:	xor    r9d,r12d
  1c054f:	mov    rax,QWORD PTR [rsp+0x80]
  1c0557:	add    r9d,eax
  1c055a:	shr    eax,0x3
  1c055d:	xor    eax,ebp
  1c055f:	mov    rdx,QWORD PTR [rsp+0x88]
  1c0567:	add    eax,edx
  1c0569:	mov    r14,rax
  1c056c:	shr    edx,0x3
  1c056f:	xor    edx,ebx
  1c0571:	mov    rdi,QWORD PTR [rsp+0xa8]
  1c0579:	mov    eax,edi
  1c057b:	rol    eax,0xf
  1c057e:	add    edx,DWORD PTR [rsp+0x68]
  1c0582:	mov    rbx,rdx
  1c0585:	mov    edx,edi
  1c0587:	rol    edx,0xd
  1c058a:	xor    edx,eax
  1c058c:	shr    edi,0xa
  1c058f:	xor    edi,edx
  1c0591:	mov    r12,QWORD PTR [rsp+0x60]
  1c0596:	add    ebx,r12d
  1c0599:	mov    r15,QWORD PTR [rsp+0x40]
  1c059e:	mov    eax,r15d
  1c05a1:	rol    eax,0xf
  1c05a4:	add    edi,ebx
  1c05a6:	mov    edx,r15d
  1c05a9:	rol    edx,0xd
  1c05ac:	xor    edx,eax
  1c05ae:	shr    r15d,0xa
  1c05b2:	xor    r15d,edx
  1c05b5:	mov    rbp,QWORD PTR [rsp+0x28]
  1c05ba:	add    r14d,ebp
  1c05bd:	mov    eax,edi
  1c05bf:	rol    eax,0xf
  1c05c2:	add    r15d,r14d
  1c05c5:	mov    edx,edi
  1c05c7:	rol    edx,0xd
  1c05ca:	xor    edx,eax
  1c05cc:	mov    ebx,r15d
  1c05cf:	rol    ebx,0xf
  1c05d2:	mov    eax,r15d
  1c05d5:	rol    eax,0xd
  1c05d8:	mov    esi,edi
  1c05da:	shr    esi,0xa
  1c05dd:	mov    r14d,r10d
  1c05e0:	rol    r14d,0x1a
  1c05e4:	xor    esi,edx
  1c05e6:	mov    edx,r10d
  1c05e9:	rol    edx,0x15
  1c05ec:	mov    r8,QWORD PTR [rsp+0x18]
  1c05f1:	add    r9d,r8d
  1c05f4:	mov    r13d,r10d
  1c05f7:	rol    r13d,0x7
  1c05fb:	mov    QWORD PTR [rsp+0x50],r13
  1c0600:	add    esi,r9d
  1c0603:	mov    QWORD PTR [rsp+0x88],rsi
  1c060b:	mov    r13d,DWORD PTR [rsp+0xb0]
  1c0613:	mov    esi,r13d
  1c0616:	rol    esi,0x19
  1c0619:	mov    DWORD PTR [rsp+0x68],esi
  1c061d:	xor    eax,ebx
  1c061f:	mov    rbx,r8
  1c0622:	mov    esi,ebx
  1c0624:	rol    esi,0x19
  1c0627:	mov    DWORD PTR [rsp+0x78],esi
  1c062b:	mov    rsi,rbp
  1c062e:	mov    r8d,ebp
  1c0631:	rol    r8d,0x19
  1c0635:	mov    DWORD PTR [rsp+0x38],r8d
  1c063a:	mov    r8d,r15d
  1c063d:	shr    r8d,0xa
  1c0641:	mov    r9,r12
  1c0644:	mov    ebp,r9d
  1c0647:	rol    ebp,0x19
  1c064a:	mov    DWORD PTR [rsp+0xb8],ebp
  1c0651:	xor    r8d,eax
  1c0654:	mov    eax,r13d
  1c0657:	rol    eax,0xe
  1c065a:	mov    ebp,eax
  1c065c:	add    ecx,r13d
  1c065f:	mov    eax,ebx
  1c0661:	rol    eax,0xe
  1c0664:	mov    ebx,eax
  1c0666:	add    r8d,ecx
  1c0669:	mov    QWORD PTR [rsp+0x80],r8
  1c0671:	mov    eax,esi
  1c0673:	rol    eax,0xe
  1c0676:	mov    ecx,eax
  1c0678:	xor    edx,r14d
  1c067b:	mov    esi,r9d
  1c067e:	rol    esi,0xe
  1c0681:	mov    rax,QWORD PTR [rsp+0x50]
  1c0686:	xor    eax,edx
  1c0688:	mov    QWORD PTR [rsp+0x50],rax
  1c068d:	mov    eax,edi
  1c068f:	rol    eax,0x19
  1c0692:	xor    ebp,DWORD PTR [rsp+0x68]
  1c0696:	mov    DWORD PTR [rsp+0x68],ebp
  1c069a:	mov    r12,QWORD PTR [rsp+0x40]
  1c069f:	mov    r14d,r12d
  1c06a2:	rol    r14d,0x19
  1c06a6:	xor    ebx,DWORD PTR [rsp+0x78]
  1c06aa:	mov    DWORD PTR [rsp+0x78],ebx
  1c06ae:	mov    r8,QWORD PTR [rsp+0xa8]
  1c06b6:	mov    r9d,r8d
  1c06b9:	rol    r9d,0x19
  1c06bd:	xor    ecx,DWORD PTR [rsp+0x38]
  1c06c1:	mov    DWORD PTR [rsp+0x38],ecx
  1c06c5:	mov    rcx,QWORD PTR [rsp+0x10]
  1c06ca:	mov    ebx,ecx
  1c06cc:	rol    ebx,0x19
  1c06cf:	xor    esi,DWORD PTR [rsp+0xb8]
  1c06d6:	mov    r13d,edi
  1c06d9:	rol    r13d,0xe
  1c06dd:	xor    r13d,eax
  1c06e0:	mov    edx,r12d
  1c06e3:	rol    edx,0xe
  1c06e6:	xor    edx,r14d
  1c06e9:	mov    eax,r8d
  1c06ec:	rol    eax,0xe
  1c06ef:	xor    eax,r9d
  1c06f2:	mov    r14d,ecx
  1c06f5:	rol    r14d,0xe
  1c06f9:	xor    r14d,ebx
  1c06fc:	mov    ebp,DWORD PTR [rsp+0x8]
  1c0700:	add    ebp,edi
  1c0702:	add    DWORD PTR [rsp+0x98],edi
  1c0709:	shr    edi,0x3
  1c070c:	xor    edi,r13d
  1c070f:	mov    r9,rdi
  1c0712:	mov    rdi,QWORD PTR [rsp+0x20]
  1c0717:	add    edi,r12d
  1c071a:	mov    QWORD PTR [rsp+0x20],rdi
  1c071f:	mov    rdi,r12
  1c0722:	add    r9d,edi
  1c0725:	mov    QWORD PTR [rsp+0x8],r9
  1c072a:	shr    edi,0x3
  1c072d:	xor    edi,edx
  1c072f:	mov    r13,QWORD PTR [rsp]
  1c0733:	mov    rdx,r8
  1c0736:	add    r13d,edx
  1c0739:	add    edi,edx
  1c073b:	mov    QWORD PTR [rsp],rdi
  1c073f:	shr    edx,0x3
  1c0742:	xor    edx,eax
  1c0744:	mov    rax,rcx
  1c0747:	mov    r12,QWORD PTR [rsp+0x48]
  1c074c:	add    r12d,eax
  1c074f:	add    edx,eax
  1c0751:	mov    DWORD PTR [rsp+0x40],edx
  1c0755:	shr    eax,0x3
  1c0758:	xor    eax,r14d
  1c075b:	mov    ecx,DWORD PTR [rsp+0xb0]
  1c0762:	add    eax,ecx
  1c0764:	mov    QWORD PTR [rsp+0x10],rax
  1c0769:	shr    ecx,0x3
  1c076c:	xor    ecx,DWORD PTR [rsp+0x68]
  1c0770:	mov    rax,QWORD PTR [rsp+0x18]
  1c0775:	add    ecx,eax
  1c0777:	mov    DWORD PTR [rsp+0x48],ecx
  1c077b:	shr    eax,0x3
  1c077e:	xor    eax,DWORD PTR [rsp+0x78]
  1c0782:	mov    rcx,QWORD PTR [rsp+0x28]
  1c0787:	add    eax,ecx
  1c0789:	mov    QWORD PTR [rsp+0x18],rax
  1c078e:	shr    ecx,0x3
  1c0791:	xor    ecx,DWORD PTR [rsp+0x38]
  1c0795:	mov    rax,QWORD PTR [rsp+0x60]
  1c079a:	add    ecx,eax
  1c079c:	mov    QWORD PTR [rsp+0x28],rcx
  1c07a1:	shr    eax,0x3
  1c07a4:	xor    eax,esi
  1c07a6:	add    eax,DWORD PTR [rsp+0x58]
  1c07aa:	add    eax,r15d
  1c07ad:	mov    QWORD PTR [rsp+0x60],rax
  1c07b2:	lea    eax,[r15+r11*1]
  1c07b6:	mov    rdx,QWORD PTR [rsp+0x70]
  1c07bb:	mov    r9d,edx
  1c07be:	xor    r9d,r11d
  1c07c1:	and    r9d,r10d
  1c07c4:	xor    r9d,r11d
  1c07c7:	add    r9d,ebp
  1c07ca:	mov    rcx,QWORD PTR [rsp+0x50]
  1c07cf:	add    r9d,ecx
  1c07d2:	add    r9d,0x19a4c116
  1c07d9:	mov    rsi,QWORD PTR [rsp+0xa0]
  1c07e1:	mov    r11d,esi
  1c07e4:	rol    r11d,0x1e
  1c07e8:	mov    ebp,esi
  1c07ea:	rol    ebp,0x13
  1c07ed:	xor    ebp,r11d
  1c07f0:	mov    r11d,esi
  1c07f3:	rol    r11d,0xa
  1c07f7:	xor    r11d,ebp
  1c07fa:	mov    r15,QWORD PTR [rsp+0xc0]
  1c0802:	mov    r14d,r15d
  1c0805:	mov    rbx,QWORD PTR [rsp+0xc8]
  1c080d:	xor    r14d,ebx
  1c0810:	and    r14d,esi
  1c0813:	mov    ebp,r15d
  1c0816:	and    ebp,ebx
  1c0818:	xor    ebp,r14d
  1c081b:	add    ebp,r11d
  1c081e:	add    ebp,r9d
  1c0821:	mov    edi,DWORD PTR [rsp+0x34]
  1c0825:	add    edi,r9d
  1c0828:	mov    r9d,edi
  1c082b:	rol    r9d,0x1a
  1c082f:	mov    r11d,edi
  1c0832:	rol    r11d,0x15
  1c0836:	xor    r11d,r9d
  1c0839:	mov    r9d,edi
  1c083c:	rol    r9d,0x7
  1c0840:	xor    r9d,r11d
  1c0843:	mov    r11d,r10d
  1c0846:	xor    r11d,edx
  1c0849:	and    r11d,edi
  1c084c:	xor    r11d,edx
  1c084f:	mov    rcx,rdx
  1c0852:	add    r11d,eax
  1c0855:	mov    eax,ebp
  1c0857:	rol    eax,0x1e
  1c085a:	add    r9d,r11d
  1c085d:	add    r9d,0x1e376c08
  1c0864:	mov    r11d,ebp
  1c0867:	rol    r11d,0x13
  1c086b:	xor    r11d,eax
  1c086e:	mov    eax,ebp
  1c0870:	rol    eax,0xa
  1c0873:	xor    eax,r11d
  1c0876:	mov    r11d,esi
  1c0879:	mov    rdx,r15
  1c087c:	and    r11d,edx
  1c087f:	mov    r15d,esi
  1c0882:	xor    r15d,edx
  1c0885:	and    r15d,ebp
  1c0888:	xor    r15d,r11d
  1c088b:	add    r15d,eax
  1c088e:	add    ebx,r9d
  1c0891:	mov    eax,ebx
  1c0893:	rol    eax,0x1a
  1c0896:	add    r15d,r9d
  1c0899:	mov    r9d,ebx
  1c089c:	rol    r9d,0x15
  1c08a0:	xor    r9d,eax
  1c08a3:	mov    eax,ebx
  1c08a5:	rol    eax,0x7
  1c08a8:	xor    eax,r9d
  1c08ab:	mov    r8,QWORD PTR [rsp+0x88]
  1c08b3:	mov    r11d,edi
  1c08b6:	xor    r11d,r10d
  1c08b9:	and    r11d,ebx
  1c08bc:	xor    r11d,r10d
  1c08bf:	add    r11d,r8d
  1c08c2:	add    r11d,ecx
  1c08c5:	add    eax,r11d
  1c08c8:	add    eax,0x2748774c
  1c08cd:	mov    r9d,r15d
  1c08d0:	rol    r9d,0x1e
  1c08d4:	mov    r11d,r15d
  1c08d7:	rol    r11d,0x13
  1c08db:	xor    r11d,r9d
  1c08de:	mov    r9d,r15d
  1c08e1:	rol    r9d,0xa
  1c08e5:	xor    r9d,r11d
  1c08e8:	mov    r14d,ebp
  1c08eb:	xor    r14d,esi
  1c08ee:	and    r14d,r15d
  1c08f1:	mov    r11d,ebp
  1c08f4:	and    r11d,esi
  1c08f7:	xor    r11d,r14d
  1c08fa:	add    r11d,r9d
  1c08fd:	add    r11d,eax
  1c0900:	add    edx,eax
  1c0902:	mov    eax,edx
  1c0904:	rol    eax,0x1a
  1c0907:	mov    r9d,edx
  1c090a:	rol    r9d,0x15
  1c090e:	xor    r9d,eax
  1c0911:	mov    eax,edx
  1c0913:	rol    eax,0x7
  1c0916:	xor    eax,r9d
  1c0919:	mov    rcx,QWORD PTR [rsp+0x80]
  1c0921:	lea    r9d,[rcx+r10*1]
  1c0925:	mov    r10d,ebx
  1c0928:	xor    r10d,edi
  1c092b:	and    r10d,edx
  1c092e:	xor    r10d,edi
  1c0931:	add    r10d,r9d
  1c0934:	mov    r9d,r11d
  1c0937:	rol    r9d,0x1e
  1c093b:	add    eax,r10d
  1c093e:	add    eax,0x34b0bcb5
  1c0943:	mov    r10d,r11d
  1c0946:	rol    r10d,0x13
  1c094a:	xor    r10d,r9d
  1c094d:	mov    r9d,r11d
  1c0950:	rol    r9d,0xa
  1c0954:	xor    r9d,r10d
  1c0957:	mov    r14d,r15d
  1c095a:	and    r14d,ebp
  1c095d:	mov    r10d,r15d
  1c0960:	xor    r10d,ebp
  1c0963:	and    r10d,r11d
  1c0966:	xor    r10d,r14d
  1c0969:	add    r10d,r9d
  1c096c:	add    r10d,eax
  1c096f:	mov    r9d,r8d
  1c0972:	rol    r9d,0xf
  1c0976:	add    esi,eax
  1c0978:	mov    eax,r8d
  1c097b:	rol    eax,0xd
  1c097e:	xor    eax,r9d
  1c0981:	mov    r9,QWORD PTR [rsp+0x28]
  1c0986:	add    r9d,r8d
  1c0989:	mov    QWORD PTR [rsp+0x28],r9
  1c098e:	mov    r9d,r8d
  1c0991:	shr    r9d,0xa
  1c0995:	xor    r9d,eax
  1c0998:	mov    eax,ecx
  1c099a:	rol    eax,0xf
  1c099d:	add    r9d,r12d
  1c09a0:	mov    r14d,ecx
  1c09a3:	rol    r14d,0xd
  1c09a7:	xor    r14d,eax
  1c09aa:	mov    rax,QWORD PTR [rsp+0x18]
  1c09af:	add    eax,ecx
  1c09b1:	mov    QWORD PTR [rsp+0x18],rax
  1c09b6:	mov    eax,ecx
  1c09b8:	shr    eax,0xa
  1c09bb:	xor    eax,r14d
  1c09be:	mov    r14d,r9d
  1c09c1:	rol    r14d,0xf
  1c09c5:	add    eax,r13d
  1c09c8:	mov    r12d,r9d
  1c09cb:	rol    r12d,0xd
  1c09cf:	xor    r12d,r14d
  1c09d2:	add    edi,r9d
  1c09d5:	add    DWORD PTR [rsp+0x48],r9d
  1c09da:	mov    r13d,r9d
  1c09dd:	shr    r13d,0xa
  1c09e1:	mov    r9d,eax
  1c09e4:	rol    r9d,0xf
  1c09e8:	xor    r13d,r12d
  1c09eb:	mov    r12d,eax
  1c09ee:	rol    r12d,0xd
  1c09f2:	add    r13d,DWORD PTR [rsp+0x20]
  1c09f7:	xor    r12d,r9d
  1c09fa:	mov    r14d,eax
  1c09fd:	shr    r14d,0xa
  1c0a01:	xor    r14d,r12d
  1c0a04:	mov    r9d,esi
  1c0a07:	rol    r9d,0x1a
  1c0a0b:	add    r14d,DWORD PTR [rsp+0x98]
  1c0a13:	mov    r12d,esi
  1c0a16:	rol    r12d,0x15
  1c0a1a:	xor    r12d,r9d
  1c0a1d:	mov    r9d,esi
  1c0a20:	rol    r9d,0x7
  1c0a24:	xor    r9d,r12d
  1c0a27:	mov    rcx,QWORD PTR [rsp+0x10]
  1c0a2c:	add    ecx,eax
  1c0a2e:	mov    QWORD PTR [rsp+0x10],rcx
  1c0a33:	add    eax,ebx
  1c0a35:	mov    r12d,edx
  1c0a38:	xor    r12d,ebx
  1c0a3b:	and    r12d,esi
  1c0a3e:	xor    r12d,ebx
  1c0a41:	add    r12d,edi
  1c0a44:	lea    edi,[r9+r12*1]
  1c0a48:	add    edi,0x391c0cb3
  1c0a4e:	mov    r8d,r10d
  1c0a51:	rol    r8d,0x1e
  1c0a55:	mov    r9d,r10d
  1c0a58:	rol    r9d,0x13
  1c0a5c:	xor    r9d,r8d
  1c0a5f:	mov    r12d,r10d
  1c0a62:	rol    r12d,0xa
  1c0a66:	xor    r12d,r9d
  1c0a69:	mov    r9d,r11d
  1c0a6c:	xor    r9d,r15d
  1c0a6f:	and    r9d,r10d
  1c0a72:	mov    r8d,r11d
  1c0a75:	and    r8d,r15d
  1c0a78:	xor    r8d,r9d
  1c0a7b:	add    r8d,r12d
  1c0a7e:	add    r8d,edi
  1c0a81:	add    ebp,edi
  1c0a83:	mov    edi,ebp
  1c0a85:	rol    edi,0x1a
  1c0a88:	mov    r9d,ebp
  1c0a8b:	rol    r9d,0x15
  1c0a8f:	xor    r9d,edi
  1c0a92:	mov    edi,ebp
  1c0a94:	rol    edi,0x7
  1c0a97:	xor    edi,r9d
  1c0a9a:	mov    r9d,esi
  1c0a9d:	xor    r9d,edx
  1c0aa0:	and    r9d,ebp
  1c0aa3:	xor    r9d,edx
  1c0aa6:	add    r9d,eax
  1c0aa9:	mov    eax,r8d
  1c0aac:	rol    eax,0x1e
  1c0aaf:	add    edi,r9d
  1c0ab2:	add    edi,0x4ed8aa4a
  1c0ab8:	mov    r9d,r8d
  1c0abb:	rol    r9d,0x13
  1c0abf:	xor    r9d,eax
  1c0ac2:	mov    eax,r8d
  1c0ac5:	rol    eax,0xa
  1c0ac8:	xor    eax,r9d
  1c0acb:	mov    r9d,r10d
  1c0ace:	and    r9d,r11d
  1c0ad1:	mov    ecx,r10d
  1c0ad4:	xor    ecx,r11d
  1c0ad7:	and    ecx,r8d
  1c0ada:	xor    ecx,r9d
  1c0add:	add    ecx,eax
  1c0adf:	add    r15d,edi
  1c0ae2:	mov    eax,r15d
  1c0ae5:	rol    eax,0x1a
  1c0ae8:	add    ecx,edi
  1c0aea:	mov    edi,r15d
  1c0aed:	rol    edi,0x15
  1c0af0:	xor    edi,eax
  1c0af2:	mov    eax,r15d
  1c0af5:	rol    eax,0x7
  1c0af8:	xor    eax,edi
  1c0afa:	mov    r9d,ebp
  1c0afd:	xor    r9d,esi
  1c0b00:	and    r9d,r15d
  1c0b03:	xor    r9d,esi
  1c0b06:	add    r9d,r13d
  1c0b09:	add    r9d,edx
  1c0b0c:	add    eax,r9d
  1c0b0f:	add    eax,0x5b9cca4f
  1c0b14:	mov    edi,ecx
  1c0b16:	rol    edi,0x1e
  1c0b19:	mov    r9d,ecx
  1c0b1c:	rol    r9d,0x13
  1c0b20:	xor    r9d,edi
  1c0b23:	mov    r12d,ecx
  1c0b26:	rol    r12d,0xa
  1c0b2a:	xor    r12d,r9d
  1c0b2d:	mov    r9d,r8d
  1c0b30:	xor    r9d,r10d
  1c0b33:	and    r9d,ecx
  1c0b36:	mov    edi,r8d
  1c0b39:	and    edi,r10d
  1c0b3c:	xor    edi,r9d
  1c0b3f:	add    edi,r12d
  1c0b42:	add    edi,eax
  1c0b44:	add    r11d,eax
  1c0b47:	mov    eax,r11d
  1c0b4a:	rol    eax,0x1a
  1c0b4d:	mov    r9d,r11d
  1c0b50:	rol    r9d,0x15
  1c0b54:	xor    r9d,eax
  1c0b57:	mov    eax,r11d
  1c0b5a:	rol    eax,0x7
  1c0b5d:	xor    eax,r9d
  1c0b60:	mov    r12d,r15d
  1c0b63:	xor    r12d,ebp
  1c0b66:	and    r12d,r11d
  1c0b69:	xor    r12d,ebp
  1c0b6c:	add    r12d,r14d
  1c0b6f:	add    r12d,esi
  1c0b72:	mov    r9d,edi
  1c0b75:	rol    r9d,0x1e
  1c0b79:	add    eax,r12d
  1c0b7c:	add    eax,0x682e6ff3
  1c0b81:	mov    r12d,edi
  1c0b84:	rol    r12d,0x13
  1c0b88:	xor    r12d,r9d
  1c0b8b:	mov    r9d,edi
  1c0b8e:	rol    r9d,0xa
  1c0b92:	xor    r9d,r12d
  1c0b95:	mov    esi,ecx
  1c0b97:	and    esi,r8d
  1c0b9a:	mov    r12d,ecx
  1c0b9d:	xor    r12d,r8d
  1c0ba0:	and    r12d,edi
  1c0ba3:	xor    r12d,esi
  1c0ba6:	add    r12d,r9d
  1c0ba9:	add    r12d,eax
  1c0bac:	mov    esi,r13d
  1c0baf:	rol    esi,0xf
  1c0bb2:	add    r10d,eax
  1c0bb5:	mov    eax,r13d
  1c0bb8:	rol    eax,0xd
  1c0bbb:	xor    eax,esi
  1c0bbd:	mov    ebx,DWORD PTR [rsp+0x40]
  1c0bc1:	add    ebx,r13d
  1c0bc4:	mov    esi,r13d
  1c0bc7:	shr    esi,0xa
  1c0bca:	xor    esi,eax
  1c0bcc:	mov    eax,r14d
  1c0bcf:	rol    eax,0xf
  1c0bd2:	add    esi,DWORD PTR [rsp+0x60]
  1c0bd6:	mov    r9d,r14d
  1c0bd9:	rol    r9d,0xd
  1c0bdd:	xor    r9d,eax
  1c0be0:	mov    rax,QWORD PTR [rsp]
  1c0be4:	add    eax,r14d
  1c0be7:	mov    QWORD PTR [rsp],rax
  1c0beb:	mov    eax,r14d
  1c0bee:	shr    eax,0xa
  1c0bf1:	xor    eax,r9d
  1c0bf4:	mov    r9d,esi
  1c0bf7:	rol    r9d,0xf
  1c0bfb:	add    eax,DWORD PTR [rsp+0x28]
  1c0bff:	mov    r14d,esi
  1c0c02:	rol    r14d,0xd
  1c0c06:	xor    r14d,r9d
  1c0c09:	add    ebp,esi
  1c0c0b:	mov    rdx,QWORD PTR [rsp+0x8]
  1c0c10:	add    edx,esi
  1c0c12:	mov    QWORD PTR [rsp+0x8],rdx
  1c0c17:	mov    r13d,esi
  1c0c1a:	shr    r13d,0xa
  1c0c1e:	mov    esi,eax
  1c0c20:	rol    esi,0xf
  1c0c23:	xor    r13d,r14d
  1c0c26:	mov    r9d,eax
  1c0c29:	rol    r9d,0xd
  1c0c2d:	add    r13d,DWORD PTR [rsp+0x18]
  1c0c32:	xor    r9d,esi
  1c0c35:	mov    r14d,eax
  1c0c38:	shr    r14d,0xa
  1c0c3c:	xor    r14d,r9d
  1c0c3f:	mov    esi,r10d
  1c0c42:	rol    esi,0x1a
  1c0c45:	add    r14d,DWORD PTR [rsp+0x48]
  1c0c4a:	mov    edx,r10d
  1c0c4d:	rol    edx,0x15
  1c0c50:	xor    edx,esi
  1c0c52:	mov    esi,r10d
  1c0c55:	rol    esi,0x7
  1c0c58:	xor    esi,edx
  1c0c5a:	add    eax,r15d
  1c0c5d:	mov    edx,r11d
  1c0c60:	xor    edx,r15d
  1c0c63:	and    edx,r10d
  1c0c66:	xor    edx,r15d
  1c0c69:	add    edx,ebp
  1c0c6b:	add    edx,esi
  1c0c6d:	add    edx,0x748f82ee
  1c0c73:	mov    esi,r12d
  1c0c76:	rol    esi,0x1e
  1c0c79:	mov    r9d,r12d
  1c0c7c:	rol    r9d,0x13
  1c0c80:	xor    r9d,esi
  1c0c83:	mov    esi,r12d
  1c0c86:	rol    esi,0xa
  1c0c89:	xor    esi,r9d
  1c0c8c:	mov    ebp,edi
  1c0c8e:	xor    ebp,ecx
  1c0c90:	and    ebp,r12d
  1c0c93:	mov    r9d,edi
  1c0c96:	and    r9d,ecx
  1c0c99:	xor    r9d,ebp
  1c0c9c:	add    r9d,esi
  1c0c9f:	add    r9d,edx
  1c0ca2:	add    r8d,edx
  1c0ca5:	mov    edx,r8d
  1c0ca8:	rol    edx,0x1a
  1c0cab:	mov    esi,r8d
  1c0cae:	rol    esi,0x15
  1c0cb1:	xor    esi,edx
  1c0cb3:	mov    edx,r8d
  1c0cb6:	rol    edx,0x7
  1c0cb9:	xor    edx,esi
  1c0cbb:	mov    esi,r10d
  1c0cbe:	xor    esi,r11d
  1c0cc1:	and    esi,r8d
  1c0cc4:	xor    esi,r11d
  1c0cc7:	add    esi,eax
  1c0cc9:	add    edx,esi
  1c0ccb:	add    edx,0x78a5636f
  1c0cd1:	mov    eax,r9d
  1c0cd4:	rol    eax,0x1e
  1c0cd7:	mov    esi,r9d
  1c0cda:	rol    esi,0x13
  1c0cdd:	xor    esi,eax
  1c0cdf:	mov    ebp,r9d
  1c0ce2:	rol    ebp,0xa
  1c0ce5:	xor    ebp,esi
  1c0ce7:	mov    esi,r12d
  1c0cea:	and    esi,edi
  1c0cec:	mov    eax,r12d
  1c0cef:	xor    eax,edi
  1c0cf1:	and    eax,r9d
  1c0cf4:	xor    eax,esi
  1c0cf6:	add    eax,ebp
  1c0cf8:	add    eax,edx
  1c0cfa:	add    ecx,edx
  1c0cfc:	mov    edx,ecx
  1c0cfe:	rol    edx,0x1a
  1c0d01:	mov    esi,ecx
  1c0d03:	rol    esi,0x15
  1c0d06:	xor    esi,edx
  1c0d08:	mov    edx,ecx
  1c0d0a:	rol    edx,0x7
  1c0d0d:	xor    edx,esi
  1c0d0f:	lea    esi,[r11+r13*1]
  1c0d13:	mov    r11d,r8d
  1c0d16:	xor    r11d,r10d
  1c0d19:	and    r11d,ecx
  1c0d1c:	xor    r11d,r10d
  1c0d1f:	mov    ebp,eax
  1c0d21:	rol    ebp,0x1e
  1c0d24:	add    r11d,esi
  1c0d27:	mov    esi,eax
  1c0d29:	rol    esi,0x13
  1c0d2c:	add    edx,r11d
  1c0d2f:	add    edx,0x84c87814
  1c0d35:	mov    r15d,eax
  1c0d38:	rol    r15d,0xa
  1c0d3c:	xor    esi,ebp
  1c0d3e:	xor    r15d,esi
  1c0d41:	mov    esi,r9d
  1c0d44:	xor    esi,r12d
  1c0d47:	and    esi,eax
  1c0d49:	mov    r11d,r9d
  1c0d4c:	and    r11d,r12d
  1c0d4f:	xor    r11d,esi
  1c0d52:	add    edi,edx
  1c0d54:	mov    esi,edi
  1c0d56:	rol    esi,0x1a
  1c0d59:	add    r11d,r15d
  1c0d5c:	mov    ebp,edi
  1c0d5e:	rol    ebp,0x15
  1c0d61:	add    r11d,edx
  1c0d64:	mov    edx,edi
  1c0d66:	rol    edx,0x7
  1c0d69:	xor    ebp,esi
  1c0d6b:	xor    edx,ebp
  1c0d6d:	lea    esi,[r14+r10*1]
  1c0d71:	mov    r10d,ecx
  1c0d74:	xor    r10d,r8d
  1c0d77:	and    r10d,edi
  1c0d7a:	xor    r10d,r8d
  1c0d7d:	add    r10d,esi
  1c0d80:	add    edx,r10d
  1c0d83:	add    edx,0x8cc70208
  1c0d89:	mov    esi,r11d
  1c0d8c:	rol    esi,0x1e
  1c0d8f:	mov    r10d,r11d
  1c0d92:	rol    r10d,0x13
  1c0d96:	xor    r10d,esi
  1c0d99:	mov    esi,r11d
  1c0d9c:	rol    esi,0xa
  1c0d9f:	xor    esi,r10d
  1c0da2:	mov    ebp,eax
  1c0da4:	and    ebp,r9d
  1c0da7:	mov    r10d,eax
  1c0daa:	xor    r10d,r9d
  1c0dad:	and    r10d,r11d
  1c0db0:	xor    r10d,ebp
  1c0db3:	add    r10d,esi
  1c0db6:	add    r10d,edx
  1c0db9:	add    r12d,edx
  1c0dbc:	mov    edx,r13d
  1c0dbf:	rol    edx,0xf
  1c0dc2:	mov    esi,r13d
  1c0dc5:	rol    esi,0xd
  1c0dc8:	xor    esi,edx
  1c0dca:	shr    r13d,0xa
  1c0dce:	mov    edx,r14d
  1c0dd1:	rol    edx,0xf
  1c0dd4:	xor    r13d,esi
  1c0dd7:	mov    esi,r14d
  1c0dda:	rol    esi,0xd
  1c0ddd:	add    r13d,DWORD PTR [rsp+0x10]
  1c0de2:	xor    esi,edx
  1c0de4:	shr    r14d,0xa
  1c0de8:	xor    r14d,esi
  1c0deb:	add    r14d,ebx
  1c0dee:	mov    edx,r13d
  1c0df1:	rol    edx,0xf
  1c0df4:	mov    esi,r13d
  1c0df7:	rol    esi,0xd
  1c0dfa:	xor    esi,edx
  1c0dfc:	mov    edx,r14d
  1c0dff:	rol    edx,0xf
  1c0e02:	mov    r15d,r13d
  1c0e05:	shr    r15d,0xa
  1c0e09:	mov    ebp,r14d
  1c0e0c:	rol    ebp,0xd
  1c0e0f:	xor    r15d,esi
  1c0e12:	xor    ebp,edx
  1c0e14:	mov    esi,r14d
  1c0e17:	shr    esi,0xa
  1c0e1a:	xor    esi,ebp
  1c0e1c:	mov    edx,r12d
  1c0e1f:	rol    edx,0x1a
  1c0e22:	add    r13d,r8d
  1c0e25:	mov    r8d,r12d
  1c0e28:	rol    r8d,0x15
  1c0e2c:	xor    r8d,edx
  1c0e2f:	mov    edx,r12d
  1c0e32:	rol    edx,0x7
  1c0e35:	xor    edx,r8d
  1c0e38:	add    r14d,ecx
  1c0e3b:	mov    r8d,edi
  1c0e3e:	xor    r8d,ecx
  1c0e41:	and    r8d,r12d
  1c0e44:	xor    r8d,ecx
  1c0e47:	add    r8d,r13d
  1c0e4a:	lea    ecx,[rdx+r8*1]
  1c0e4e:	add    ecx,0x90befffa
  1c0e54:	mov    edx,r10d
  1c0e57:	rol    edx,0x1e
  1c0e5a:	mov    r8d,r10d
  1c0e5d:	rol    r8d,0x13
  1c0e61:	xor    r8d,edx
  1c0e64:	mov    ebp,r10d
  1c0e67:	rol    ebp,0xa
  1c0e6a:	xor    ebp,r8d
  1c0e6d:	mov    r8d,r11d
  1c0e70:	xor    r8d,eax
  1c0e73:	and    r8d,r10d
  1c0e76:	mov    edx,r11d
  1c0e79:	and    edx,eax
  1c0e7b:	xor    edx,r8d
  1c0e7e:	add    edx,ebp
  1c0e80:	add    edx,ecx
  1c0e82:	add    r9d,ecx
  1c0e85:	mov    ecx,r9d
  1c0e88:	rol    ecx,0x1a
  1c0e8b:	mov    r8d,r9d
  1c0e8e:	rol    r8d,0x15
  1c0e92:	xor    r8d,ecx
  1c0e95:	mov    ecx,r9d
  1c0e98:	rol    ecx,0x7
  1c0e9b:	xor    ecx,r8d
  1c0e9e:	mov    r8d,r12d
  1c0ea1:	xor    r8d,edi
  1c0ea4:	and    r8d,r9d
  1c0ea7:	xor    r8d,edi
  1c0eaa:	add    r8d,r14d
  1c0ead:	add    ecx,r8d
  1c0eb0:	add    ecx,0xa4506ceb
  1c0eb6:	mov    r8d,edx
  1c0eb9:	rol    r8d,0x1e
  1c0ebd:	mov    ebp,edx
  1c0ebf:	rol    ebp,0x13
  1c0ec2:	xor    ebp,r8d
  1c0ec5:	mov    r14d,edx
  1c0ec8:	rol    r14d,0xa
  1c0ecc:	xor    r14d,ebp
  1c0ecf:	mov    ebp,r10d
  1c0ed2:	and    ebp,r11d
  1c0ed5:	mov    r8d,r10d
  1c0ed8:	xor    r8d,r11d
  1c0edb:	and    r8d,edx
  1c0ede:	xor    r8d,ebp
  1c0ee1:	add    r8d,r14d
  1c0ee4:	add    r8d,ecx
  1c0ee7:	add    eax,ecx
  1c0ee9:	mov    ecx,eax
  1c0eeb:	rol    ecx,0x1a
  1c0eee:	mov    ebp,eax
  1c0ef0:	rol    ebp,0x15
  1c0ef3:	xor    ebp,ecx
  1c0ef5:	mov    ecx,eax
  1c0ef7:	rol    ecx,0x7
  1c0efa:	xor    ecx,ebp
  1c0efc:	mov    rbx,QWORD PTR [rsp]
  1c0f00:	add    ebx,r15d
  1c0f03:	add    ebx,edi
  1c0f05:	mov    edi,r9d
  1c0f08:	xor    edi,r12d
  1c0f0b:	and    edi,eax
  1c0f0d:	xor    edi,r12d
  1c0f10:	add    ebx,edi
  1c0f12:	lea    edi,[rcx+rbx*1]
  1c0f15:	add    edi,0xbef9a3f7
  1c0f1b:	mov    ecx,r8d
  1c0f1e:	rol    ecx,0x1e
  1c0f21:	mov    ebx,r8d
  1c0f24:	rol    ebx,0x13
  1c0f27:	xor    ebx,ecx
  1c0f29:	mov    ebp,r8d
  1c0f2c:	rol    ebp,0xa
  1c0f2f:	xor    ebp,ebx
  1c0f31:	mov    ebx,edx
  1c0f33:	xor    ebx,r10d
  1c0f36:	and    ebx,r8d
  1c0f39:	mov    ecx,edx
  1c0f3b:	and    ecx,r10d
  1c0f3e:	xor    ecx,ebx
  1c0f40:	add    ecx,ebp
  1c0f42:	add    ecx,edi
  1c0f44:	add    r11d,edi
  1c0f47:	mov    edi,r11d
  1c0f4a:	rol    edi,0x1a
  1c0f4d:	mov    ebx,r11d
  1c0f50:	rol    ebx,0x15
  1c0f53:	xor    ebx,edi
  1c0f55:	mov    edi,r11d
  1c0f58:	rol    edi,0x7
  1c0f5b:	xor    edi,ebx
  1c0f5d:	mov    rbx,QWORD PTR [rsp+0x8]
  1c0f62:	add    ebx,esi
  1c0f64:	add    ebx,r12d
  1c0f67:	mov    r14,rbx
  1c0f6a:	mov    esi,eax
  1c0f6c:	xor    esi,r9d
  1c0f6f:	and    esi,r11d
  1c0f72:	xor    esi,r9d
  1c0f75:	mov    ebx,ecx
  1c0f77:	rol    ebx,0x1e
  1c0f7a:	add    r14d,esi
  1c0f7d:	mov    ebp,ecx
  1c0f7f:	rol    ebp,0x13
  1c0f82:	lea    esi,[rdi+r14*1]
  1c0f86:	add    esi,0xc67178f2
  1c0f8c:	mov    r14d,ecx
  1c0f8f:	rol    r14d,0xa
  1c0f93:	xor    ebp,ebx
  1c0f95:	xor    r14d,ebp
  1c0f98:	mov    ebx,r8d
  1c0f9b:	and    ebx,edx
  1c0f9d:	mov    edi,r8d
  1c0fa0:	xor    edi,edx
  1c0fa2:	and    edi,ecx
  1c0fa4:	xor    edi,ebx
  1c0fa6:	add    edi,DWORD PTR [rsp+0x118]
  1c0fad:	add    edi,r14d
  1c0fb0:	add    ecx,DWORD PTR [rsp+0x120]
  1c0fb7:	add    edi,esi
  1c0fb9:	add    r8d,DWORD PTR [rsp+0xd0]
  1c0fc1:	add    edx,DWORD PTR [rsp+0xd8]
  1c0fc8:	add    r10d,DWORD PTR [rsp+0x130]
  1c0fd0:	add    r10d,esi
  1c0fd3:	add    r11d,DWORD PTR [rsp+0x128]
  1c0fdb:	add    eax,DWORD PTR [rsp+0x110]
  1c0fe2:	add    DWORD PTR [rsp+0xe4],r9d
  1c0fea:	mov    r9d,DWORD PTR [rsp+0xe4]
  1c0ff2:	mov    rsi,QWORD PTR [rsp+0x100]
  1c0ffa:	add    rsi,0x40
  1c0ffe:	mov    r12d,edi
  1c1001:	mov    r14d,ecx
  1c1004:	mov    ebx,r8d
  1c1007:	mov    QWORD PTR [rsp+0xd0],rbx
  1c100f:	mov    ebx,edx
  1c1011:	mov    QWORD PTR [rsp+0xd8],rbx
  1c1019:	mov    ebp,r10d
  1c101c:	mov    r13d,r11d
  1c101f:	mov    r15d,eax
  1c1022:	mov    rbx,rsi
  1c1025:	cmp    rsi,QWORD PTR [rsp+0x108]
  1c102d:	jne    1be530 <sha2::sha256::compress256+0x90>
  1c1033:	jmp    1c1059 <sha2::sha256::compress256+0x2bb9>
  1c1035:	mov    eax,r15d
  1c1038:	mov    r11d,r13d
  1c103b:	mov    r10d,ebp
  1c103e:	mov    rcx,QWORD PTR [rsp+0xd8]
  1c1046:	mov    edx,ecx
  1c1048:	mov    rcx,QWORD PTR [rsp+0xd0]
  1c1050:	mov    r8d,ecx
  1c1053:	mov    ecx,r14d
  1c1056:	mov    edi,r12d
  1c1059:	mov    rsi,QWORD PTR [rsp+0xe8]
  1c1061:	mov    DWORD PTR [rsi],edi
  1c1063:	mov    DWORD PTR [rsi+0x4],ecx
  1c1066:	mov    DWORD PTR [rsi+0x8],r8d
  1c106a:	mov    DWORD PTR [rsi+0xc],edx
  1c106d:	mov    DWORD PTR [rsi+0x10],r10d
  1c1071:	mov    DWORD PTR [rsi+0x14],r11d
  1c1075:	mov    DWORD PTR [rsi+0x18],eax
  1c1078:	mov    DWORD PTR [rsi+0x1c],r9d
  1c107c:	add    rsp,0x138
  1c1083:	pop    rbx
  1c1084:	pop    r12
  1c1086:	pop    r13
  1c1088:	pop    r14
  1c108a:	pop    r15
  1c108c:	pop    rbp
  1c108d:	ret
  1c108e:	mov    r14,rdx
  1c1091:	call   1c10d0 <sha2::sha256::x86::shani_cpuid::init_get::init_inner>
  1c1096:	mov    rdx,r14
  1c1099:	test   al,al
  1c109b:	je     1be4d9 <sha2::sha256::compress256+0x39>
  1c10a1:	mov    rdi,QWORD PTR [rsp+0xe8]
  1c10a9:	mov    rsi,rbx
  1c10ac:	add    rsp,0x138
  1c10b3:	pop    rbx
  1c10b4:	pop    r12
  1c10b6:	pop    r13
  1c10b8:	pop    r14
  1c10ba:	pop    r15
  1c10bc:	pop    rbp
  1c10bd:	jmp    1c1120 <sha2::sha256::x86::digest_blocks>
  1c10c2:	int3
  1c10c3:	int3
  1c10c4:	int3
  1c10c5:	int3
  1c10c6:	int3
  1c10c7:	int3
  1c10c8:	int3
  1c10c9:	int3
  1c10ca:	int3
  1c10cb:	int3
  1c10cc:	int3
  1c10cd:	int3
  1c10ce:	int3
  1c10cf:	int3

00000000001c1120 <sha2::sha256::x86::digest_blocks>:
  1c1120:	movdqu xmm0,XMMWORD PTR [rdi]
  1c1124:	movdqu xmm1,XMMWORD PTR [rdi+0x10]
  1c1129:	pshufd xmm0,xmm0,0xb1
  1c112e:	pshufd xmm12,xmm1,0x1b
  1c1134:	movdqa xmm13,xmm0
  1c1139:	palignr xmm13,xmm12,0x8
  1c1140:	pblendw xmm12,xmm0,0xf0
  1c1147:	test   rdx,rdx
  1c114a:	je     1c14b6 <sha2::sha256::x86::digest_blocks+0x396>
  1c1150:	shl    rdx,0x6
  1c1154:	add    rdx,rsi
  1c1157:	movdqa xmm5,XMMWORD PTR [rip+0xffffffffffe72e41]        # 33fa0 <anon.19cf9f7b7bd5f5377953b3f4a1d5ab20.0.llvm.1952225316318715181+0x220>
  1c115f:	movdqa xmm9,XMMWORD PTR [rip+0xffffffffffe72778]        # 338e0 <anon.813ecba9df73225402e1b2a70d3f32e6.22.llvm.699389136448165060+0x469>
  1c1168:	movdqa xmm10,XMMWORD PTR [rip+0xffffffffffe72a8f]        # 33c00 <anon.813ecba9df73225402e1b2a70d3f32e6.22.llvm.699389136448165060+0x789>
  1c1171:	movdqa xmm11,XMMWORD PTR [rip+0xffffffffffe729a6]        # 33b20 <anon.813ecba9df73225402e1b2a70d3f32e6.22.llvm.699389136448165060+0x6a9>
  1c117a:	nop    WORD PTR [rax+rax*1+0x0]
  1c1180:	movdqu xmm7,XMMWORD PTR [rsi]
  1c1184:	movdqu xmm14,XMMWORD PTR [rsi+0x10]
  1c118a:	movdqu xmm2,XMMWORD PTR [rsi+0x20]
  1c118f:	pshufb xmm7,xmm5
  1c1194:	pshufb xmm14,xmm5
  1c119a:	movdqa xmm0,xmm7
  1c119e:	paddd  xmm0,XMMWORD PTR [rip+0xffffffffffe7280a]        # 339b0 <anon.813ecba9df73225402e1b2a70d3f32e6.22.llvm.699389136448165060+0x539>
  1c11a6:	movdqa xmm3,xmm12
  1c11ab:	sha256rnds2 xmm3,xmm13,xmm0
  1c11b0:	pshufd xmm0,xmm0,0xe
  1c11b5:	movdqa xmm4,xmm13
  1c11ba:	sha256rnds2 xmm4,xmm3,xmm0
  1c11be:	movdqa xmm0,xmm14
  1c11c3:	paddd  xmm0,XMMWORD PTR [rip+0xffffffffffe725a5]        # 33770 <anon.813ecba9df73225402e1b2a70d3f32e6.22.llvm.699389136448165060+0x2f9>
  1c11cb:	pshufb xmm2,xmm5
  1c11d0:	sha256rnds2 xmm3,xmm4,xmm0
  1c11d4:	pshufd xmm0,xmm0,0xe
  1c11d9:	sha256rnds2 xmm4,xmm3,xmm0
  1c11dd:	movdqa xmm0,xmm2
  1c11e1:	paddd  xmm0,XMMWORD PTR [rip+0xffffffffffe72bf7]        # 33de0 <anon.19cf9f7b7bd5f5377953b3f4a1d5ab20.0.llvm.1952225316318715181+0x60>
  1c11e9:	movdqu xmm8,XMMWORD PTR [rsi+0x30]
  1c11ef:	sha256rnds2 xmm3,xmm4,xmm0
  1c11f3:	pshufd xmm0,xmm0,0xe
  1c11f8:	pshufb xmm8,xmm5
  1c11fe:	sha256rnds2 xmm4,xmm3,xmm0
  1c1202:	movdqa xmm0,xmm8
  1c1207:	paddd  xmm0,XMMWORD PTR [rip+0xffffffffffe73061]        # 34270 <anon.19cf9f7b7bd5f5377953b3f4a1d5ab20.0.llvm.1952225316318715181+0x4f0>
  1c120f:	pshufd xmm1,xmm0,0xe
  1c1214:	sha256msg1 xmm7,xmm14
  1c1219:	sha256rnds2 xmm3,xmm4,xmm0
  1c121d:	movdqa xmm6,xmm8
  1c1222:	palignr xmm6,xmm2,0x4
  1c1228:	movdqa xmm0,xmm1
  1c122c:	sha256rnds2 xmm4,xmm3,xmm0
  1c1230:	paddd  xmm6,xmm7
  1c1234:	sha256msg2 xmm6,xmm8
  1c1239:	movdqa xmm0,xmm6
  1c123d:	paddd  xmm0,XMMWORD PTR [rip+0xffffffffffe72d1b]        # 33f60 <anon.19cf9f7b7bd5f5377953b3f4a1d5ab20.0.llvm.1952225316318715181+0x1e0>
  1c1245:	pshufd xmm1,xmm0,0xe
  1c124a:	sha256msg1 xmm14,xmm2
  1c124f:	sha256rnds2 xmm3,xmm4,xmm0
  1c1253:	movdqa xmm7,xmm6
  1c1257:	palignr xmm7,xmm8,0x4
  1c125e:	movdqa xmm0,xmm1
  1c1262:	sha256rnds2 xmm4,xmm3,xmm0
  1c1266:	paddd  xmm7,xmm14
  1c126b:	sha256msg2 xmm7,xmm6
  1c126f:	movdqa xmm0,xmm7
  1c1273:	paddd  xmm0,XMMWORD PTR [rip+0xffffffffffe73005]        # 34280 <anon.19cf9f7b7bd5f5377953b3f4a1d5ab20.0.llvm.1952225316318715181+0x500>
  1c127b:	pshufd xmm1,xmm0,0xe
  1c1280:	sha256msg1 xmm2,xmm8
  1c1285:	sha256rnds2 xmm3,xmm4,xmm0
  1c1289:	movdqa xmm15,xmm7
  1c128e:	palignr xmm15,xmm6,0x4
  1c1295:	movdqa xmm0,xmm1
  1c1299:	sha256rnds2 xmm4,xmm3,xmm0
  1c129d:	paddd  xmm15,xmm2
  1c12a2:	sha256msg2 xmm15,xmm7
  1c12a7:	movdqa xmm0,xmm15
  1c12ac:	paddd  xmm0,XMMWORD PTR [rip+0xffffffffffe72b3c]        # 33df0 <anon.19cf9f7b7bd5f5377953b3f4a1d5ab20.0.llvm.1952225316318715181+0x70>
  1c12b4:	sha256rnds2 xmm3,xmm4,xmm0
  1c12b8:	sha256msg1 xmm8,xmm6
  1c12bd:	movdqa xmm2,xmm15
  1c12c2:	palignr xmm2,xmm7,0x4
  1c12c8:	paddd  xmm2,xmm8
  1c12cd:	sha256msg2 xmm2,xmm15
  1c12d2:	pshufd xmm0,xmm0,0xe
  1c12d7:	movdqa xmm8,xmm2
  1c12dc:	paddd  xmm8,XMMWORD PTR [rip+0xffffffffffe72bcb]        # 33eb0 <anon.19cf9f7b7bd5f5377953b3f4a1d5ab20.0.llvm.1952225316318715181+0x130>
  1c12e5:	sha256rnds2 xmm4,xmm3,xmm0
  1c12e9:	movdqa xmm0,xmm8
  1c12ee:	sha256rnds2 xmm3,xmm4,xmm0
  1c12f2:	sha256msg1 xmm6,xmm7
  1c12f6:	movdqa xmm1,xmm2
  1c12fa:	palignr xmm1,xmm15,0x4
  1c1301:	paddd  xmm1,xmm6
  1c1305:	sha256msg2 xmm1,xmm2
  1c1309:	pshufd xmm0,xmm8,0xe
  1c130f:	movdqa xmm6,xmm1
  1c1313:	paddd  xmm6,XMMWORD PTR [rip+0xffffffffffe72de5]        # 34100 <anon.19cf9f7b7bd5f5377953b3f4a1d5ab20.0.llvm.1952225316318715181+0x380>
  1c131b:	sha256rnds2 xmm4,xmm3,xmm0
  1c131f:	movdqa xmm0,xmm6
  1c1323:	sha256rnds2 xmm3,xmm4,xmm0
  1c1327:	sha256msg1 xmm7,xmm15
  1c132c:	movdqa xmm14,xmm1
  1c1331:	palignr xmm14,xmm2,0x4
  1c1338:	paddd  xmm14,xmm7
  1c133d:	sha256msg2 xmm14,xmm1
  1c1342:	pshufd xmm0,xmm6,0xe
  1c1347:	movdqa xmm6,xmm14
  1c134c:	sha256msg1 xmm15,xmm2
  1c1351:	sha256rnds2 xmm4,xmm3,xmm0
  1c1355:	movdqa xmm7,xmm14
  1c135a:	palignr xmm7,xmm1,0x4
  1c1360:	paddd  xmm7,xmm15
  1c1365:	paddd  xmm6,XMMWORD PTR [rip+0xffffffffffe72b53]        # 33ec0 <anon.19cf9f7b7bd5f5377953b3f4a1d5ab20.0.llvm.1952225316318715181+0x140>
  1c136d:	pshufd xmm15,xmm6,0xe
  1c1373:	sha256msg2 xmm7,xmm14
  1c1378:	movdqa xmm0,xmm6
  1c137c:	sha256rnds2 xmm3,xmm4,xmm0
  1c1380:	sha256msg1 xmm2,xmm1
  1c1384:	movdqa xmm6,xmm7
  1c1388:	palignr xmm6,xmm14,0x4
  1c138f:	paddd  xmm6,xmm2
  1c1393:	movdqa xmm2,xmm7
  1c1397:	paddd  xmm2,XMMWORD PTR [rip+0xffffffffffe72771]        # 33b10 <anon.813ecba9df73225402e1b2a70d3f32e6.22.llvm.699389136448165060+0x699>
  1c139f:	movdqa xmm0,xmm15
  1c13a4:	sha256rnds2 xmm4,xmm3,xmm0
  1c13a8:	sha256msg2 xmm6,xmm7
  1c13ac:	sha256msg1 xmm1,xmm14
  1c13b1:	movdqa xmm0,xmm2
  1c13b5:	sha256rnds2 xmm3,xmm4,xmm0
  1c13b9:	movdqa xmm8,xmm6
  1c13be:	palignr xmm8,xmm7,0x4
  1c13c5:	paddd  xmm8,xmm1
  1c13ca:	pshufd xmm0,xmm2,0xe
  1c13cf:	movdqa xmm1,xmm6
  1c13d3:	paddd  xmm1,XMMWORD PTR [rip+0xffffffffffe72675]        # 33a50 <anon.813ecba9df73225402e1b2a70d3f32e6.22.llvm.699389136448165060+0x5d9>
  1c13db:	sha256rnds2 xmm4,xmm3,xmm0
  1c13df:	sha256msg2 xmm8,xmm6
  1c13e4:	sha256msg1 xmm14,xmm7
  1c13e9:	movdqa xmm0,xmm1
  1c13ed:	sha256rnds2 xmm3,xmm4,xmm0
  1c13f1:	movdqa xmm2,xmm8
  1c13f6:	palignr xmm2,xmm6,0x4
  1c13fc:	paddd  xmm2,xmm14
  1c1401:	pshufd xmm0,xmm1,0xe
  1c1406:	sha256msg2 xmm2,xmm8
  1c140b:	sha256msg1 xmm7,xmm6
  1c140f:	sha256rnds2 xmm4,xmm3,xmm0
  1c1413:	movdqa xmm14,xmm2
  1c1418:	palignr xmm14,xmm8,0x4
  1c141f:	sha256msg1 xmm6,xmm8
  1c1424:	movdqa xmm0,xmm8
  1c1429:	paddd  xmm0,XMMWORD PTR [rip+0xffffffffffe727bf]        # 33bf0 <anon.813ecba9df73225402e1b2a70d3f32e6.22.llvm.699389136448165060+0x779>
  1c1431:	sha256rnds2 xmm3,xmm4,xmm0
  1c1435:	pshufd xmm0,xmm0,0xe
  1c143a:	paddd  xmm14,xmm7
  1c143f:	sha256msg2 xmm14,xmm2
  1c1444:	sha256rnds2 xmm4,xmm3,xmm0
  1c1448:	movdqa xmm1,xmm14
  1c144d:	palignr xmm1,xmm2,0x4
  1c1453:	movdqa xmm0,xmm2
  1c1457:	paddd  xmm0,xmm9
  1c145c:	sha256rnds2 xmm3,xmm4,xmm0
  1c1460:	pshufd xmm0,xmm0,0xe
  1c1465:	sha256rnds2 xmm4,xmm3,xmm0
  1c1469:	paddd  xmm1,xmm6
  1c146d:	sha256msg2 xmm1,xmm14
  1c1472:	movdqa xmm0,xmm14
  1c1477:	paddd  xmm0,xmm10
  1c147c:	sha256rnds2 xmm3,xmm4,xmm0
  1c1480:	pshufd xmm0,xmm0,0xe
  1c1485:	sha256rnds2 xmm4,xmm3,xmm0
  1c1489:	paddd  xmm1,xmm11
  1c148e:	movdqa xmm0,xmm1
  1c1492:	sha256rnds2 xmm3,xmm4,xmm0
  1c1496:	pshufd xmm0,xmm1,0xe
  1c149b:	sha256rnds2 xmm4,xmm3,xmm0
  1c149f:	paddd  xmm13,xmm4
  1c14a4:	paddd  xmm12,xmm3
  1c14a9:	add    rsi,0x40
  1c14ad:	cmp    rsi,rdx
  1c14b0:	jne    1c1180 <sha2::sha256::x86::digest_blocks+0x60>
  1c14b6:	pshufd xmm0,xmm13,0x1b
  1c14bc:	pshufd xmm1,xmm12,0xb1
  1c14c2:	movdqa xmm2,xmm0
  1c14c6:	pblendw xmm2,xmm1,0xf0
  1c14cc:	palignr xmm1,xmm0,0x8
  1c14d2:	movdqu XMMWORD PTR [rdi],xmm2
  1c14d6:	movdqu XMMWORD PTR [rdi+0x10],xmm1
  1c14db:	ret
  1c14dc:	int3
  1c14dd:	int3
  1c14de:	int3
  1c14df:	int3
