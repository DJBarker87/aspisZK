0000000000037700 <pv_dudect::kernels::state_only_hiding::measure_m31>:
   37700:	push   rbp
   37701:	push   r15
   37703:	push   r14
   37705:	push   r13
   37707:	push   r12
   37709:	push   rbx
   3770a:	sub    rsp,0x88
   37711:	mov    rbx,rdi
   37714:	mov    rcx,QWORD PTR [rdi+0x50]
   37718:	mov    r12,QWORD PTR [rdi]
   3771b:	mov    r13,QWORD PTR [rdi+0x28]
   3771f:	lea    rbp,[rdi+0x8]
   37723:	lea    r14,[rdi+0x30]
   37727:	mov    r15d,0x10
   3772d:	nop    DWORD PTR [rax]
   37730:	cmp    rcx,0x8
   37734:	je     37770 <pv_dudect::kernels::state_only_hiding::measure_m31+0x70>
   37736:	lea    rdi,[rcx*4+0x0]
   3773e:	inc    rcx
   37741:	mov    QWORD PTR [rbx+0x50],rcx
   37745:	cmp    rdi,0x20
   37749:	jae    3783a <pv_dudect::kernels::state_only_hiding::measure_m31+0x13a>
   3774f:	mov    eax,DWORD PTR [r14+rdi*1]
   37753:	and    eax,0x7fffffff
   37758:	cmp    rax,0x7fffffff
   3775e:	je     3780e <pv_dudect::kernels::state_only_hiding::measure_m31+0x10e>
   37764:	jmp    3781e <pv_dudect::kernels::state_only_hiding::measure_m31+0x11e>
   37769:	nop    DWORD PTR [rax+0x0]
   37770:	movups xmm0,XMMWORD PTR [rbp+0x0]
   37774:	movups xmm1,XMMWORD PTR [rbp+0x10]
   37778:	movaps XMMWORD PTR [rsp+0x50],xmm1
   3777d:	movaps XMMWORD PTR [rsp+0x40],xmm0
   37782:	mov    QWORD PTR [rsp+0x8],r13
   37787:	lea    rax,[rip+0xfffffffffffe3b22]        # 1b2b0 <anon.cc9e1b464619ab62d021e6446458583c.0.llvm.15800808401943094617+0x1c>
   3778e:	mov    QWORD PTR [rsp+0x10],rax
   37793:	mov    QWORD PTR [rsp+0x18],0x27
   3779c:	lea    rax,[rsp+0x40]
   377a1:	mov    QWORD PTR [rsp+0x20],rax
   377a6:	mov    QWORD PTR [rsp+0x28],0x20
   377af:	lea    rax,[rsp+0x8]
   377b4:	mov    QWORD PTR [rsp+0x30],rax
   377b9:	mov    QWORD PTR [rsp+0x38],0x8
   377c2:	mov    edx,0x3
   377c7:	lea    rdi,[rsp+0x68]
   377cc:	lea    rsi,[rsp+0x10]
   377d1:	call   r12
   377d4:	movups xmm0,XMMWORD PTR [rsp+0x68]
   377d9:	movups xmm1,XMMWORD PTR [rsp+0x78]
   377de:	movups XMMWORD PTR [r14+0x10],xmm1
   377e3:	movups XMMWORD PTR [r14],xmm0
   377e7:	inc    r13
   377ea:	mov    QWORD PTR [rbx+0x28],r13
   377ee:	mov    QWORD PTR [rbx+0x50],0x1
   377f6:	mov    ecx,0x1
   377fb:	xor    edi,edi
   377fd:	mov    eax,DWORD PTR [r14+rdi*1]
   37801:	and    eax,0x7fffffff
   37806:	cmp    rax,0x7fffffff
   3780c:	jne    3781e <pv_dudect::kernels::state_only_hiding::measure_m31+0x11e>
   3780e:	dec    r15
   37811:	jne    37730 <pv_dudect::kernels::state_only_hiding::measure_m31+0x30>
   37817:	mov    eax,0x201
   3781c:	jmp    37828 <pv_dudect::kernels::state_only_hiding::measure_m31+0x128>
   3781e:	shl    rax,0x20
   37822:	or     rax,0x200
   37828:	add    rsp,0x88
   3782f:	pop    rbx
   37830:	pop    r12
   37832:	pop    r13
   37834:	pop    r14
   37836:	pop    r15
   37838:	pop    rbp
   37839:	ret
   3783a:	lea    rsi,[rdi+0x4]
   3783e:	lea    rcx,[rip+0x535db]        # 8ae20 <anon.cc9e1b464619ab62d021e6446458583c.4.llvm.15800808401943094617+0x30>
   37845:	mov    edx,0x20
   3784a:	call   QWORD PTR [rip+0x55e68]        # 8d6b8 <_DYNAMIC+0x378>

0000000000037850 <pv_dudect::kernels::state_only_hiding::measure_qm31>:
   37850:	push   rbp
   37851:	push   r15
   37853:	push   r14
   37855:	push   r13
   37857:	push   r12
   37859:	push   rbx
   3785a:	sub    rsp,0x98
   37861:	mov    r14,rsi
   37864:	mov    QWORD PTR [rsp+0x8],rdi
   37869:	mov    rax,QWORD PTR [rsi+0x50]
   3786d:	mov    rcx,QWORD PTR [rsi]
   37870:	mov    QWORD PTR [rsp+0x18],rcx
   37875:	mov    rdx,QWORD PTR [rsi+0x28]
   37879:	lea    rcx,[rsi+0x8]
   3787d:	mov    QWORD PTR [rsp+0x10],rcx
   37882:	lea    r15,[rsi+0x30]
   37886:	mov    ebx,0x10
   3788b:	lea    r12,[rsp+0x20]
   37890:	mov    ebp,0x7fffffff
   37895:	data16 cs nop WORD PTR [rax+rax*1+0x0]
   378a0:	cmp    rax,0x8
   378a4:	je     378e0 <pv_dudect::kernels::state_only_hiding::measure_qm31+0x90>
   378a6:	lea    rdi,[rax*4+0x0]
   378ae:	inc    rax
   378b1:	mov    QWORD PTR [r14+0x50],rax
   378b5:	cmp    rdi,0x20
   378b9:	jae    37ce4 <pv_dudect::kernels::state_only_hiding::measure_qm31+0x494>
   378bf:	mov    r13d,DWORD PTR [r15+rdi*1]
   378c3:	and    r13d,ebp
   378c6:	cmp    r13d,0x7fffffff
   378cd:	je     37986 <pv_dudect::kernels::state_only_hiding::measure_qm31+0x136>
   378d3:	jmp    37994 <pv_dudect::kernels::state_only_hiding::measure_qm31+0x144>
   378d8:	nop    DWORD PTR [rax+rax*1+0x0]
   378e0:	mov    rax,QWORD PTR [rsp+0x10]
   378e5:	movups xmm0,XMMWORD PTR [rax]
   378e8:	movups xmm1,XMMWORD PTR [rax+0x10]
   378ec:	movaps XMMWORD PTR [rsp+0x60],xmm1
   378f1:	movaps XMMWORD PTR [rsp+0x50],xmm0
   378f6:	mov    QWORD PTR [rsp],rdx
   378fa:	lea    rax,[rip+0xfffffffffffe39af]        # 1b2b0 <anon.cc9e1b464619ab62d021e6446458583c.0.llvm.15800808401943094617+0x1c>
   37901:	mov    QWORD PTR [rsp+0x20],rax
   37906:	mov    QWORD PTR [rsp+0x28],0x27
   3790f:	lea    rax,[rsp+0x50]
   37914:	mov    QWORD PTR [rsp+0x30],rax
   37919:	mov    QWORD PTR [rsp+0x38],0x20
   37922:	mov    rax,rsp
   37925:	mov    QWORD PTR [rsp+0x40],rax
   3792a:	mov    QWORD PTR [rsp+0x48],0x8
   37933:	mov    r13,rdx
   37936:	mov    edx,0x3
   3793b:	lea    rdi,[rsp+0x70]
   37940:	mov    rsi,r12
   37943:	call   QWORD PTR [rsp+0x18]
   37947:	mov    rdx,r13
   3794a:	movups xmm0,XMMWORD PTR [rsp+0x70]
   3794f:	movups xmm1,XMMWORD PTR [rsp+0x80]
   37957:	movups XMMWORD PTR [r15+0x10],xmm1
   3795c:	movups XMMWORD PTR [r15],xmm0
   37960:	inc    rdx
   37963:	mov    QWORD PTR [r14+0x28],rdx
   37967:	mov    QWORD PTR [r14+0x50],0x1
   3796f:	mov    eax,0x1
   37974:	xor    edi,edi
   37976:	mov    r13d,DWORD PTR [r15+rdi*1]
   3797a:	and    r13d,ebp
   3797d:	cmp    r13d,0x7fffffff
   37984:	jne    37994 <pv_dudect::kernels::state_only_hiding::measure_qm31+0x144>
   37986:	dec    rbx
   37989:	jne    378a0 <pv_dudect::kernels::state_only_hiding::measure_qm31+0x50>
   3798f:	jmp    37cae <pv_dudect::kernels::state_only_hiding::measure_qm31+0x45e>
   37994:	mov    ebx,0x10
   37999:	mov    ebp,0x7fffffff
   3799e:	xchg   ax,ax
   379a0:	cmp    rax,0x8
   379a4:	je     379e0 <pv_dudect::kernels::state_only_hiding::measure_qm31+0x190>
   379a6:	lea    rdi,[rax*4+0x0]
   379ae:	inc    rax
   379b1:	mov    QWORD PTR [r14+0x50],rax
   379b5:	cmp    rdi,0x20
   379b9:	jae    37ce4 <pv_dudect::kernels::state_only_hiding::measure_qm31+0x494>
   379bf:	mov    r12d,DWORD PTR [r15+rdi*1]
   379c3:	and    r12d,ebp
   379c6:	cmp    r12d,0x7fffffff
   379cd:	je     37a88 <pv_dudect::kernels::state_only_hiding::measure_qm31+0x238>
   379d3:	jmp    37a96 <pv_dudect::kernels::state_only_hiding::measure_qm31+0x246>
   379d8:	nop    DWORD PTR [rax+rax*1+0x0]
   379e0:	mov    rax,QWORD PTR [rsp+0x10]
   379e5:	movups xmm0,XMMWORD PTR [rax]
   379e8:	movups xmm1,XMMWORD PTR [rax+0x10]
   379ec:	movaps XMMWORD PTR [rsp+0x60],xmm1
   379f1:	movaps XMMWORD PTR [rsp+0x50],xmm0
   379f6:	mov    QWORD PTR [rsp],rdx
   379fa:	lea    rax,[rip+0xfffffffffffe38af]        # 1b2b0 <anon.cc9e1b464619ab62d021e6446458583c.0.llvm.15800808401943094617+0x1c>
   37a01:	mov    QWORD PTR [rsp+0x20],rax
   37a06:	mov    QWORD PTR [rsp+0x28],0x27
   37a0f:	lea    rax,[rsp+0x50]
   37a14:	mov    QWORD PTR [rsp+0x30],rax
   37a19:	mov    QWORD PTR [rsp+0x38],0x20
   37a22:	mov    rax,rsp
   37a25:	mov    QWORD PTR [rsp+0x40],rax
   37a2a:	mov    QWORD PTR [rsp+0x48],0x8
   37a33:	mov    r12,rdx
   37a36:	mov    edx,0x3
   37a3b:	lea    rdi,[rsp+0x70]
   37a40:	lea    rsi,[rsp+0x20]
   37a45:	call   QWORD PTR [rsp+0x18]
   37a49:	mov    rdx,r12
   37a4c:	movups xmm0,XMMWORD PTR [rsp+0x70]
   37a51:	movups xmm1,XMMWORD PTR [rsp+0x80]
   37a59:	movups XMMWORD PTR [r15+0x10],xmm1
   37a5e:	movups XMMWORD PTR [r15],xmm0
   37a62:	inc    rdx
   37a65:	mov    QWORD PTR [r14+0x28],rdx
   37a69:	mov    QWORD PTR [r14+0x50],0x1
   37a71:	mov    eax,0x1
   37a76:	xor    edi,edi
   37a78:	mov    r12d,DWORD PTR [r15+rdi*1]
   37a7c:	and    r12d,ebp
   37a7f:	cmp    r12d,0x7fffffff
   37a86:	jne    37a96 <pv_dudect::kernels::state_only_hiding::measure_qm31+0x246>
   37a88:	dec    rbx
   37a8b:	jne    379a0 <pv_dudect::kernels::state_only_hiding::measure_qm31+0x150>
   37a91:	jmp    37cae <pv_dudect::kernels::state_only_hiding::measure_qm31+0x45e>
   37a96:	mov    ebp,0x10
   37a9b:	mov    ecx,0x7fffffff
   37aa0:	cmp    rax,0x8
   37aa4:	je     37ae0 <pv_dudect::kernels::state_only_hiding::measure_qm31+0x290>
   37aa6:	lea    rdi,[rax*4+0x0]
   37aae:	inc    rax
   37ab1:	mov    QWORD PTR [r14+0x50],rax
   37ab5:	cmp    rdi,0x20
   37ab9:	jae    37ce4 <pv_dudect::kernels::state_only_hiding::measure_qm31+0x494>
   37abf:	mov    ebx,DWORD PTR [r15+rdi*1]
   37ac3:	and    ebx,ecx
   37ac5:	cmp    ebx,0x7fffffff
   37acb:	je     37b8b <pv_dudect::kernels::state_only_hiding::measure_qm31+0x33b>
   37ad1:	jmp    37b99 <pv_dudect::kernels::state_only_hiding::measure_qm31+0x349>
   37ad6:	cs nop WORD PTR [rax+rax*1+0x0]
   37ae0:	mov    rax,QWORD PTR [rsp+0x10]
   37ae5:	movups xmm0,XMMWORD PTR [rax]
   37ae8:	movups xmm1,XMMWORD PTR [rax+0x10]
   37aec:	movaps XMMWORD PTR [rsp+0x60],xmm1
   37af1:	movaps XMMWORD PTR [rsp+0x50],xmm0
   37af6:	mov    QWORD PTR [rsp],rdx
   37afa:	lea    rax,[rip+0xfffffffffffe37af]        # 1b2b0 <anon.cc9e1b464619ab62d021e6446458583c.0.llvm.15800808401943094617+0x1c>
   37b01:	mov    QWORD PTR [rsp+0x20],rax
   37b06:	mov    QWORD PTR [rsp+0x28],0x27
   37b0f:	lea    rax,[rsp+0x50]
   37b14:	mov    QWORD PTR [rsp+0x30],rax
   37b19:	mov    QWORD PTR [rsp+0x38],0x20
   37b22:	mov    rax,rsp
   37b25:	mov    QWORD PTR [rsp+0x40],rax
   37b2a:	mov    QWORD PTR [rsp+0x48],0x8
   37b33:	mov    rbx,rdx
   37b36:	mov    edx,0x3
   37b3b:	lea    rdi,[rsp+0x70]
   37b40:	lea    rsi,[rsp+0x20]
   37b45:	call   QWORD PTR [rsp+0x18]
   37b49:	mov    ecx,0x7fffffff
   37b4e:	mov    rdx,rbx
   37b51:	movups xmm0,XMMWORD PTR [rsp+0x70]
   37b56:	movups xmm1,XMMWORD PTR [rsp+0x80]
   37b5e:	movups XMMWORD PTR [r15+0x10],xmm1
   37b63:	movups XMMWORD PTR [r15],xmm0
   37b67:	inc    rdx
   37b6a:	mov    QWORD PTR [r14+0x28],rdx
   37b6e:	mov    QWORD PTR [r14+0x50],0x1
   37b76:	mov    eax,0x1
   37b7b:	xor    edi,edi
   37b7d:	mov    ebx,DWORD PTR [r15+rdi*1]
   37b81:	and    ebx,ecx
   37b83:	cmp    ebx,0x7fffffff
   37b89:	jne    37b99 <pv_dudect::kernels::state_only_hiding::measure_qm31+0x349>
   37b8b:	dec    rbp
   37b8e:	jne    37aa0 <pv_dudect::kernels::state_only_hiding::measure_qm31+0x250>
   37b94:	jmp    37cae <pv_dudect::kernels::state_only_hiding::measure_qm31+0x45e>
   37b99:	mov    ebp,0x10
   37b9e:	mov    esi,0x7fffffff
   37ba3:	data16 data16 data16 cs nop WORD PTR [rax+rax*1+0x0]
   37bb0:	cmp    rax,0x8
   37bb4:	je     37bf0 <pv_dudect::kernels::state_only_hiding::measure_qm31+0x3a0>
   37bb6:	lea    rdi,[rax*4+0x0]
   37bbe:	inc    rax
   37bc1:	mov    QWORD PTR [r14+0x50],rax
   37bc5:	cmp    rdi,0x20
   37bc9:	jae    37ce4 <pv_dudect::kernels::state_only_hiding::measure_qm31+0x494>
   37bcf:	mov    ecx,DWORD PTR [r15+rdi*1]
   37bd3:	and    ecx,esi
   37bd5:	cmp    ecx,0x7fffffff
   37bdb:	je     37ca5 <pv_dudect::kernels::state_only_hiding::measure_qm31+0x455>
   37be1:	jmp    37ccd <pv_dudect::kernels::state_only_hiding::measure_qm31+0x47d>
   37be6:	cs nop WORD PTR [rax+rax*1+0x0]
   37bf0:	mov    rax,QWORD PTR [rsp+0x10]
   37bf5:	movups xmm0,XMMWORD PTR [rax]
   37bf8:	movups xmm1,XMMWORD PTR [rax+0x10]
   37bfc:	movaps XMMWORD PTR [rsp+0x60],xmm1
   37c01:	movaps XMMWORD PTR [rsp+0x50],xmm0
   37c06:	mov    QWORD PTR [rsp],rdx
   37c0a:	lea    rax,[rip+0xfffffffffffe369f]        # 1b2b0 <anon.cc9e1b464619ab62d021e6446458583c.0.llvm.15800808401943094617+0x1c>
   37c11:	mov    QWORD PTR [rsp+0x20],rax
   37c16:	mov    QWORD PTR [rsp+0x28],0x27
   37c1f:	lea    rax,[rsp+0x50]
   37c24:	mov    QWORD PTR [rsp+0x30],rax
   37c29:	mov    QWORD PTR [rsp+0x38],0x20
   37c32:	mov    rax,rsp
   37c35:	mov    QWORD PTR [rsp+0x40],rax
   37c3a:	mov    QWORD PTR [rsp+0x48],0x8
   37c43:	mov    QWORD PTR [rsp+0x90],rdx
   37c4b:	mov    edx,0x3
   37c50:	lea    rdi,[rsp+0x70]
   37c55:	lea    rsi,[rsp+0x20]
   37c5a:	call   QWORD PTR [rsp+0x18]
   37c5e:	mov    esi,0x7fffffff
   37c63:	mov    rdx,QWORD PTR [rsp+0x90]
   37c6b:	movups xmm0,XMMWORD PTR [rsp+0x70]
   37c70:	movups xmm1,XMMWORD PTR [rsp+0x80]
   37c78:	movups XMMWORD PTR [r15+0x10],xmm1
   37c7d:	movups XMMWORD PTR [r15],xmm0
   37c81:	inc    rdx
   37c84:	mov    QWORD PTR [r14+0x28],rdx
   37c88:	mov    QWORD PTR [r14+0x50],0x1
   37c90:	mov    eax,0x1
   37c95:	xor    edi,edi
   37c97:	mov    ecx,DWORD PTR [r15+rdi*1]
   37c9b:	and    ecx,esi
   37c9d:	cmp    ecx,0x7fffffff
   37ca3:	jne    37ccd <pv_dudect::kernels::state_only_hiding::measure_qm31+0x47d>
   37ca5:	dec    rbp
   37ca8:	jne    37bb0 <pv_dudect::kernels::state_only_hiding::measure_qm31+0x360>
   37cae:	mov    rax,QWORD PTR [rsp+0x8]
   37cb3:	mov    BYTE PTR [rax+0x1],0x2
   37cb7:	mov    cl,0x1
   37cb9:	mov    BYTE PTR [rax],cl
   37cbb:	add    rsp,0x98
   37cc2:	pop    rbx
   37cc3:	pop    r12
   37cc5:	pop    r13
   37cc7:	pop    r14
   37cc9:	pop    r15
   37ccb:	pop    rbp
   37ccc:	ret
   37ccd:	mov    rax,QWORD PTR [rsp+0x8]
   37cd2:	mov    DWORD PTR [rax+0x4],r13d
   37cd6:	mov    DWORD PTR [rax+0x8],r12d
   37cda:	mov    DWORD PTR [rax+0xc],ebx
   37cdd:	mov    DWORD PTR [rax+0x10],ecx
   37ce0:	xor    ecx,ecx
   37ce2:	jmp    37cb9 <pv_dudect::kernels::state_only_hiding::measure_qm31+0x469>
   37ce4:	lea    rsi,[rdi+0x4]
   37ce8:	lea    rcx,[rip+0x53131]        # 8ae20 <anon.cc9e1b464619ab62d021e6446458583c.4.llvm.15800808401943094617+0x30>
   37cef:	mov    edx,0x20
   37cf4:	call   QWORD PTR [rip+0x559be]        # 8d6b8 <_DYNAMIC+0x378>
   37cfa:	int3
   37cfb:	int3
   37cfc:	int3
   37cfd:	int3
   37cfe:	int3
   37cff:	int3

000000000003f910 <aspis_prover::host_hashv>:
   3f910:	push   rbp
   3f911:	push   r15
   3f913:	push   r14
   3f915:	push   r13
   3f917:	push   r12
   3f919:	push   rbx
   3f91a:	sub    rsp,0x138
   3f921:	mov    QWORD PTR [rsp+0x70],rdi
   3f926:	xorps  xmm0,xmm0
   3f929:	movups XMMWORD PTR [rsp+0x58],xmm0
   3f92e:	movups XMMWORD PTR [rsp+0x48],xmm0
   3f933:	movups XMMWORD PTR [rsp+0x38],xmm0
   3f938:	movups XMMWORD PTR [rsp+0x28],xmm0
   3f93d:	mov    BYTE PTR [rsp+0x68],0x0
   3f942:	movups xmm0,XMMWORD PTR [rip+0xfffffffffffe11b7]        # 20b00 <anon.4542838882158fab56838ae26b7212f7.176.llvm.13126917640099348842>
   3f949:	movaps XMMWORD PTR [rsp],xmm0
   3f94d:	movups xmm0,XMMWORD PTR [rip+0xfffffffffffe11bc]        # 20b10 <anon.4542838882158fab56838ae26b7212f7.176.llvm.13126917640099348842+0x10>
   3f954:	movaps XMMWORD PTR [rsp+0x10],xmm0
   3f959:	mov    QWORD PTR [rsp+0x20],0x0
   3f962:	test   rdx,rdx
   3f965:	je     3fa74 <aspis_prover::host_hashv+0x164>
   3f96b:	mov    r14,rdx
   3f96e:	mov    r15,rsi
   3f971:	shl    r14,0x4
   3f975:	add    r14,rsi
   3f978:	xor    r12d,r12d
   3f97b:	jmp    3f9ad <aspis_prover::host_hashv+0x9d>
   3f97d:	nop    DWORD PTR [rax]
   3f980:	lea    rax,[rsp+0x28]
   3f985:	lea    rdi,[rax+r13*1]
   3f989:	mov    rsi,rbx
   3f98c:	mov    rdx,rbp
   3f98f:	call   QWORD PTR [rip+0x4dc5b]        # 8d5f0 <memcpy@GLIBC_2.14>
   3f995:	add    rbp,r13
   3f998:	mov    r12,rbp
   3f99b:	mov    BYTE PTR [rsp+0x68],r12b
   3f9a0:	add    r15,0x10
   3f9a4:	cmp    r15,r14
   3f9a7:	je     3fa74 <aspis_prover::host_hashv+0x164>
   3f9ad:	mov    rbx,QWORD PTR [r15]
   3f9b0:	mov    rbp,QWORD PTR [r15+0x8]
   3f9b4:	movzx  r13d,r12b
   3f9b8:	mov    edx,0x40
   3f9bd:	sub    rdx,r13
   3f9c0:	mov    r12,rbp
   3f9c3:	sub    r12,rdx
   3f9c6:	jb     3f980 <aspis_prover::host_hashv+0x70>
   3f9c8:	test   r13,r13
   3f9cb:	je     3fa69 <aspis_prover::host_hashv+0x159>
   3f9d1:	lea    rax,[rbx+rdx*1]
   3f9d5:	mov    QWORD PTR [rsp+0x78],rax
   3f9da:	mov    rbp,r14
   3f9dd:	lea    r14,[rsp+0x28]
   3f9e2:	add    r13,r14
   3f9e5:	mov    rdi,r13
   3f9e8:	mov    rsi,rbx
   3f9eb:	call   QWORD PTR [rip+0x4dbff]        # 8d5f0 <memcpy@GLIBC_2.14>
   3f9f1:	inc    QWORD PTR [rsp+0x20]
   3f9f6:	mov    edx,0x1
   3f9fb:	mov    rdi,rsp
   3f9fe:	mov    rsi,r14
   3fa01:	mov    r14,rbp
   3fa04:	call   QWORD PTR [rip+0x4de6e]        # 8d878 <_DYNAMIC+0x538>
   3fa0a:	mov    rbx,QWORD PTR [rsp+0x78]
   3fa0f:	cmp    r12,0x40
   3fa13:	jb     3fa2d <aspis_prover::host_hashv+0x11d>
   3fa15:	mov    rdx,r12
   3fa18:	shr    rdx,0x6
   3fa1c:	add    QWORD PTR [rsp+0x20],rdx
   3fa21:	mov    rdi,rsp
   3fa24:	mov    rsi,rbx
   3fa27:	call   QWORD PTR [rip+0x4de4b]        # 8d878 <_DYNAMIC+0x538>
   3fa2d:	mov    rax,r12
   3fa30:	movabs rcx,0x7fffffffffffffc0
   3fa3a:	and    rax,rcx
   3fa3d:	and    r12d,0x3f
   3fa41:	add    rbx,rax
   3fa44:	lea    rdi,[rsp+0x28]
   3fa49:	mov    rsi,rbx
   3fa4c:	mov    rdx,r12
   3fa4f:	call   QWORD PTR [rip+0x4db9b]        # 8d5f0 <memcpy@GLIBC_2.14>
   3fa55:	mov    BYTE PTR [rsp+0x68],r12b
   3fa5a:	add    r15,0x10
   3fa5e:	cmp    r15,r14
   3fa61:	jne    3f9ad <aspis_prover::host_hashv+0x9d>
   3fa67:	jmp    3fa74 <aspis_prover::host_hashv+0x164>
   3fa69:	mov    r12,rbp
   3fa6c:	cmp    r12,0x40
   3fa70:	jae    3fa15 <aspis_prover::host_hashv+0x105>
   3fa72:	jmp    3fa2d <aspis_prover::host_hashv+0x11d>
   3fa74:	mov    rax,QWORD PTR [rsp+0x60]
   3fa79:	mov    QWORD PTR [rsp+0xe0],rax
   3fa81:	movzx  eax,BYTE PTR [rsp+0x68]
   3fa86:	mov    BYTE PTR [rsp+0xe8],al
   3fa8d:	mov    eax,DWORD PTR [rsp+0x69]
   3fa91:	mov    DWORD PTR [rsp+0xe9],eax
   3fa98:	movzx  eax,WORD PTR [rsp+0x6d]
   3fa9d:	mov    WORD PTR [rsp+0xed],ax
   3faa5:	movzx  eax,BYTE PTR [rsp+0x6f]
   3faaa:	mov    BYTE PTR [rsp+0xef],al
   3fab1:	movdqa xmm0,XMMWORD PTR [rsp]
   3fab6:	movaps xmm1,XMMWORD PTR [rsp+0x10]
   3fabb:	mov    rax,QWORD PTR [rsp+0x20]
   3fac0:	mov    rcx,QWORD PTR [rsp+0x28]
   3fac5:	movaps xmm2,XMMWORD PTR [rsp+0x30]
   3faca:	mov    QWORD PTR [rsp+0xa0],rax
   3fad2:	mov    QWORD PTR [rsp+0xa8],rcx
   3fada:	movaps xmm3,XMMWORD PTR [rsp+0x50]
   3fadf:	movaps XMMWORD PTR [rsp+0xd0],xmm3
   3fae7:	movaps xmm3,XMMWORD PTR [rsp+0x40]
   3faec:	movaps XMMWORD PTR [rsp+0xc0],xmm3
   3faf4:	movaps XMMWORD PTR [rsp+0xb0],xmm2
   3fafc:	movaps XMMWORD PTR [rsp+0x90],xmm1
   3fb04:	movdqa XMMWORD PTR [rsp+0x80],xmm0
   3fb0d:	lea    rbx,[rsp+0xa8]
   3fb15:	movzx  r14d,BYTE PTR [rsp+0xe8]
   3fb1e:	mov    rax,QWORD PTR [rsp+0xa0]
   3fb26:	shl    rax,0x9
   3fb2a:	lea    r15d,[r14*8+0x0]
   3fb32:	or     r15,rax
   3fb35:	bswap  r15
   3fb38:	mov    BYTE PTR [rsp+r14*1+0xa8],0x80
   3fb41:	cmp    r14d,0x3f
   3fb45:	je     3fb6e <aspis_prover::host_hashv+0x25e>
   3fb47:	lea    rdi,[rsp+r14*1]
   3fb4b:	add    rdi,0xa8
   3fb52:	inc    rdi
   3fb55:	mov    rdx,r14
   3fb58:	xor    rdx,0x3f
   3fb5c:	xor    esi,esi
   3fb5e:	call   QWORD PTR [rip+0x4dccc]        # 8d830 <memset@GLIBC_2.2.5>
   3fb64:	xor    r14d,0x38
   3fb68:	cmp    r14d,0x7
   3fb6c:	ja     3fbd3 <aspis_prover::host_hashv+0x2c3>
   3fb6e:	mov    r12,QWORD PTR [rip+0x4dd03]        # 8d878 <_DYNAMIC+0x538>
   3fb75:	lea    r14,[rsp+0x80]
   3fb7d:	mov    edx,0x1
   3fb82:	mov    rdi,r14
   3fb85:	mov    rsi,rbx
   3fb88:	call   r12
   3fb8b:	pxor   xmm0,xmm0
   3fb8f:	movdqa XMMWORD PTR [rsp+0x110],xmm0
   3fb98:	movdqa XMMWORD PTR [rsp+0x100],xmm0
   3fba1:	movdqa XMMWORD PTR [rsp+0xf0],xmm0
   3fbaa:	mov    QWORD PTR [rsp+0x120],0x0
   3fbb6:	mov    QWORD PTR [rsp+0x128],r15
   3fbbe:	lea    rsi,[rsp+0xf0]
   3fbc6:	mov    edx,0x1
   3fbcb:	mov    rdi,r14
   3fbce:	call   r12
   3fbd1:	jmp    3fbf1 <aspis_prover::host_hashv+0x2e1>
   3fbd3:	mov    QWORD PTR [rsp+0xe0],r15
   3fbdb:	lea    rdi,[rsp+0x80]
   3fbe3:	mov    edx,0x1
   3fbe8:	mov    rsi,rbx
   3fbeb:	call   QWORD PTR [rip+0x4dc87]        # 8d878 <_DYNAMIC+0x538>
   3fbf1:	pxor   xmm0,xmm0
   3fbf5:	movdqa xmm1,XMMWORD PTR [rsp+0x80]
   3fbfe:	movdqa xmm2,XMMWORD PTR [rsp+0x90]
   3fc07:	movdqa xmm3,xmm1
   3fc0b:	punpckhbw xmm3,xmm0
   3fc0f:	pshuflw xmm3,xmm3,0x1b
   3fc14:	pshufhw xmm3,xmm3,0x1b
   3fc19:	punpcklbw xmm1,xmm0
   3fc1d:	pshuflw xmm1,xmm1,0x1b
   3fc22:	pshufhw xmm1,xmm1,0x1b
   3fc27:	packuswb xmm1,xmm3
   3fc2b:	movdqa xmm3,xmm2
   3fc2f:	punpckhbw xmm3,xmm0
   3fc33:	pshuflw xmm3,xmm3,0x1b
   3fc38:	pshufhw xmm3,xmm3,0x1b
   3fc3d:	punpcklbw xmm2,xmm0
   3fc41:	pshuflw xmm0,xmm2,0x1b
   3fc46:	pshufhw xmm0,xmm0,0x1b
   3fc4b:	packuswb xmm0,xmm3
   3fc4f:	mov    rax,QWORD PTR [rsp+0x70]
   3fc54:	movdqu XMMWORD PTR [rax],xmm1
   3fc58:	movdqu XMMWORD PTR [rax+0x10],xmm0
   3fc5d:	add    rsp,0x138
   3fc64:	pop    rbx
   3fc65:	pop    r12
   3fc67:	pop    r13
   3fc69:	pop    r14
   3fc6b:	pop    r15
   3fc6d:	pop    rbp
   3fc6e:	ret
   3fc6f:	int3

000000000003fc70 <sha2::sha256::compress256>:
   3fc70:	push   rbp
   3fc71:	push   r15
   3fc73:	push   r14
   3fc75:	push   r13
   3fc77:	push   r12
   3fc79:	push   rbx
   3fc7a:	sub    rsp,0x138
   3fc81:	mov    rbx,rsi
   3fc84:	mov    QWORD PTR [rsp+0xe8],rdi
   3fc8c:	movzx  eax,BYTE PTR [rip+0x4e38d]        # 8e020 <sha2::sha256::x86::shani_cpuid::STORAGE>
   3fc93:	cmp    al,0x1
   3fc95:	je     42871 <sha2::sha256::compress256+0x2c01>
   3fc9b:	movzx  eax,al
   3fc9e:	cmp    eax,0xff
   3fca3:	je     4285e <sha2::sha256::compress256+0x2bee>
   3fca9:	mov    rax,QWORD PTR [rsp+0xe8]
   3fcb1:	mov    r12d,DWORD PTR [rax]
   3fcb4:	mov    r14d,DWORD PTR [rax+0x4]
   3fcb8:	mov    ecx,DWORD PTR [rax+0x8]
   3fcbb:	mov    QWORD PTR [rsp+0xd0],rcx
   3fcc3:	mov    ecx,DWORD PTR [rax+0xc]
   3fcc6:	mov    QWORD PTR [rsp+0xd8],rcx
   3fcce:	mov    ebp,DWORD PTR [rax+0x10]
   3fcd1:	mov    r13d,DWORD PTR [rax+0x14]
   3fcd5:	mov    r15d,DWORD PTR [rax+0x18]
   3fcd9:	mov    r9d,DWORD PTR [rax+0x1c]
   3fcdd:	test   rdx,rdx
   3fce0:	je     42805 <sha2::sha256::compress256+0x2b95>
   3fce6:	shl    rdx,0x6
   3fcea:	add    rdx,rbx
   3fced:	mov    QWORD PTR [rsp+0x108],rdx
   3fcf5:	data16 cs nop WORD PTR [rax+rax*1+0x0]
   3fd00:	mov    QWORD PTR [rsp+0x120],r14
   3fd08:	mov    edi,r9d
   3fd0b:	mov    DWORD PTR [rsp+0xe4],r9d
   3fd13:	mov    eax,DWORD PTR [rbx]
   3fd15:	mov    ecx,DWORD PTR [rbx+0x4]
   3fd18:	bswap  eax
   3fd1a:	mov    rsi,rax
   3fd1d:	mov    eax,ebp
   3fd1f:	rol    eax,0x1a
   3fd22:	bswap  ecx
   3fd24:	mov    r8,rcx
   3fd27:	mov    QWORD PTR [rsp+0x60],rcx
   3fd2c:	mov    ecx,ebp
   3fd2e:	rol    ecx,0x15
   3fd31:	xor    ecx,eax
   3fd33:	mov    eax,ebp
   3fd35:	rol    eax,0x7
   3fd38:	xor    eax,ecx
   3fd3a:	mov    r9,r15
   3fd3d:	mov    QWORD PTR [rsp+0x110],r15
   3fd45:	mov    edx,r9d
   3fd48:	mov    QWORD PTR [rsp+0x128],r13
   3fd50:	xor    edx,r13d
   3fd53:	and    edx,ebp
   3fd55:	xor    edx,r9d
   3fd58:	add    edx,edi
   3fd5a:	add    edx,eax
   3fd5c:	mov    QWORD PTR [rsp+0x48],rsi
   3fd61:	lea    ecx,[rsi+rdx*1]
   3fd64:	add    ecx,0x428a2f98
   3fd6a:	mov    eax,r12d
   3fd6d:	rol    eax,0x1e
   3fd70:	add    edx,esi
   3fd72:	mov    esi,r12d
   3fd75:	rol    esi,0x13
   3fd78:	xor    esi,eax
   3fd7a:	mov    eax,r12d
   3fd7d:	rol    eax,0xa
   3fd80:	xor    eax,esi
   3fd82:	mov    r10,QWORD PTR [rsp+0xd0]
   3fd8a:	mov    QWORD PTR [rsp+0xd0],r10
   3fd92:	mov    esi,r10d
   3fd95:	xor    esi,r14d
   3fd98:	and    esi,r12d
   3fd9b:	mov    edi,r10d
   3fd9e:	and    edi,r14d
   3fda1:	xor    edi,esi
   3fda3:	add    edi,eax
   3fda5:	mov    rax,QWORD PTR [rsp+0xd8]
   3fdad:	mov    QWORD PTR [rsp+0xd8],rax
   3fdb5:	add    eax,edx
   3fdb7:	add    eax,0x428a2f98
   3fdbc:	mov    edx,eax
   3fdbe:	rol    edx,0x1a
   3fdc1:	add    edi,ecx
   3fdc3:	mov    ecx,eax
   3fdc5:	rol    ecx,0x15
   3fdc8:	xor    ecx,edx
   3fdca:	mov    edx,eax
   3fdcc:	rol    edx,0x7
   3fdcf:	xor    edx,ecx
   3fdd1:	mov    ecx,r13d
   3fdd4:	xor    ecx,ebp
   3fdd6:	and    ecx,eax
   3fdd8:	xor    ecx,r13d
   3fddb:	add    ecx,r15d
   3fdde:	add    ecx,r8d
   3fde1:	lea    esi,[rcx+rdx*1]
   3fde4:	add    ecx,edx
   3fde6:	add    ecx,0x71374491
   3fdec:	mov    edx,edi
   3fdee:	rol    edx,0x1e
   3fdf1:	mov    r8d,edi
   3fdf4:	rol    r8d,0x13
   3fdf8:	xor    r8d,edx
   3fdfb:	mov    edx,edi
   3fdfd:	rol    edx,0xa
   3fe00:	xor    edx,r8d
   3fe03:	mov    r8d,r14d
   3fe06:	and    r8d,r12d
   3fe09:	mov    r9d,r14d
   3fe0c:	xor    r9d,r12d
   3fe0f:	and    r9d,edi
   3fe12:	xor    r9d,r8d
   3fe15:	add    r9d,edx
   3fe18:	add    r9d,ecx
   3fe1b:	lea    ecx,[r10+rsi*1]
   3fe1f:	add    ecx,0x71374491
   3fe25:	mov    edx,ecx
   3fe27:	rol    edx,0x1a
   3fe2a:	mov    esi,ecx
   3fe2c:	rol    esi,0x15
   3fe2f:	xor    esi,edx
   3fe31:	mov    r8d,ecx
   3fe34:	rol    r8d,0x7
   3fe38:	xor    r8d,esi
   3fe3b:	mov    r15,rbx
   3fe3e:	mov    edx,DWORD PTR [rbx+0x8]
   3fe41:	bswap  edx
   3fe43:	mov    QWORD PTR [rsp+0x88],rdx
   3fe4b:	mov    esi,eax
   3fe4d:	xor    esi,ebp
   3fe4f:	and    esi,ecx
   3fe51:	xor    esi,ebp
   3fe53:	add    esi,r13d
   3fe56:	add    esi,edx
   3fe58:	mov    r10d,r9d
   3fe5b:	rol    r10d,0x1e
   3fe5f:	lea    ebx,[rsi+r8*1]
   3fe63:	add    esi,r8d
   3fe66:	add    esi,0xb5c0fbcf
   3fe6c:	mov    r8d,r9d
   3fe6f:	rol    r8d,0x13
   3fe73:	xor    r8d,r10d
   3fe76:	mov    r10d,r9d
   3fe79:	rol    r10d,0xa
   3fe7d:	xor    r10d,r8d
   3fe80:	mov    r8d,edi
   3fe83:	mov    rdx,r12
   3fe86:	xor    r8d,edx
   3fe89:	and    r8d,r9d
   3fe8c:	mov    r11d,edi
   3fe8f:	and    r11d,edx
   3fe92:	mov    QWORD PTR [rsp+0x118],r12
   3fe9a:	xor    r11d,r8d
   3fe9d:	add    r11d,r10d
   3fea0:	lea    r10d,[r14+rbx*1]
   3fea4:	add    r10d,0xb5c0fbcf
   3feab:	mov    r8d,r10d
   3feae:	rol    r8d,0x1a
   3feb2:	add    r11d,esi
   3feb5:	mov    esi,r10d
   3feb8:	rol    esi,0x15
   3febb:	xor    esi,r8d
   3febe:	mov    r8d,r10d
   3fec1:	rol    r8d,0x7
   3fec5:	xor    r8d,esi
   3fec8:	mov    esi,DWORD PTR [r15+0xc]
   3fecc:	mov    r13,r15
   3fecf:	bswap  esi
   3fed1:	mov    QWORD PTR [rsp+0x78],rsi
   3fed6:	mov    ebx,ecx
   3fed8:	xor    ebx,eax
   3feda:	and    ebx,r10d
   3fedd:	xor    ebx,eax
   3fedf:	mov    QWORD PTR [rsp+0x130],rbp
   3fee7:	add    ebp,esi
   3fee9:	add    ebx,ebp
   3feeb:	mov    r14d,r11d
   3feee:	rol    r14d,0x1e
   3fef2:	mov    r15d,r11d
   3fef5:	rol    r15d,0x13
   3fef9:	lea    r12d,[rbx+r8*1]
   3fefd:	add    r8d,ebx
   3ff00:	add    r8d,0xe9b5dba5
   3ff07:	mov    ebp,r11d
   3ff0a:	rol    ebp,0xa
   3ff0d:	xor    r15d,r14d
   3ff10:	xor    ebp,r15d
   3ff13:	mov    ebx,r9d
   3ff16:	and    ebx,edi
   3ff18:	mov    r15d,r9d
   3ff1b:	xor    r15d,edi
   3ff1e:	and    r15d,r11d
   3ff21:	xor    r15d,ebx
   3ff24:	lea    ebx,[rdx+r12*1]
   3ff28:	add    ebx,0xe9b5dba5
   3ff2e:	mov    r14d,ebx
   3ff31:	rol    r14d,0x1a
   3ff35:	add    r15d,ebp
   3ff38:	mov    ebp,ebx
   3ff3a:	rol    ebp,0x15
   3ff3d:	add    r15d,r8d
   3ff40:	mov    r8d,ebx
   3ff43:	rol    r8d,0x7
   3ff47:	xor    ebp,r14d
   3ff4a:	xor    r8d,ebp
   3ff4d:	mov    edx,DWORD PTR [r13+0x10]
   3ff51:	bswap  edx
   3ff53:	mov    DWORD PTR [rsp+0x58],edx
   3ff57:	mov    ebp,r10d
   3ff5a:	xor    ebp,ecx
   3ff5c:	and    ebp,ebx
   3ff5e:	xor    ebp,ecx
   3ff60:	add    eax,edx
   3ff62:	mov    r14d,r15d
   3ff65:	rol    r14d,0x1e
   3ff69:	add    eax,ebp
   3ff6b:	mov    ebp,r15d
   3ff6e:	rol    ebp,0x13
   3ff71:	add    eax,r8d
   3ff74:	add    eax,0x3956c25b
   3ff79:	mov    r12d,r15d
   3ff7c:	rol    r12d,0xa
   3ff80:	xor    ebp,r14d
   3ff83:	xor    r12d,ebp
   3ff86:	mov    ebp,r11d
   3ff89:	xor    ebp,r9d
   3ff8c:	and    ebp,r15d
   3ff8f:	mov    r8d,r11d
   3ff92:	and    r8d,r9d
   3ff95:	xor    r8d,ebp
   3ff98:	add    edi,eax
   3ff9a:	mov    ebp,edi
   3ff9c:	rol    ebp,0x1a
   3ff9f:	add    r8d,r12d
   3ffa2:	mov    r14d,edi
   3ffa5:	rol    r14d,0x15
   3ffa9:	add    r8d,eax
   3ffac:	mov    eax,edi
   3ffae:	rol    eax,0x7
   3ffb1:	xor    r14d,ebp
   3ffb4:	xor    eax,r14d
   3ffb7:	mov    edx,DWORD PTR [r13+0x14]
   3ffbb:	bswap  edx
   3ffbd:	mov    QWORD PTR [rsp+0x50],rdx
   3ffc2:	add    ecx,edx
   3ffc4:	mov    r14d,ebx
   3ffc7:	xor    r14d,r10d
   3ffca:	and    r14d,edi
   3ffcd:	xor    r14d,r10d
   3ffd0:	mov    ebp,r8d
   3ffd3:	rol    ebp,0x1e
   3ffd6:	add    r14d,ecx
   3ffd9:	mov    ecx,r8d
   3ffdc:	rol    ecx,0x13
   3ffdf:	add    eax,r14d
   3ffe2:	add    eax,0x59f111f1
   3ffe7:	mov    r14d,r8d
   3ffea:	rol    r14d,0xa
   3ffee:	xor    ecx,ebp
   3fff0:	xor    r14d,ecx
   3fff3:	mov    ecx,r15d
   3fff6:	and    ecx,r11d
   3fff9:	mov    r12d,r15d
   3fffc:	xor    r12d,r11d
   3ffff:	and    r12d,r8d
   40002:	xor    r12d,ecx
   40005:	add    r9d,eax
   40008:	mov    ecx,r9d
   4000b:	rol    ecx,0x1a
   4000e:	add    r12d,r14d
   40011:	mov    ebp,r9d
   40014:	rol    ebp,0x15
   40017:	add    r12d,eax
   4001a:	mov    eax,r9d
   4001d:	rol    eax,0x7
   40020:	xor    ebp,ecx
   40022:	xor    eax,ebp
   40024:	mov    ecx,DWORD PTR [r13+0x18]
   40028:	bswap  ecx
   4002a:	mov    QWORD PTR [rsp+0x38],rcx
   4002f:	add    ecx,r10d
   40032:	mov    r10d,edi
   40035:	xor    r10d,ebx
   40038:	and    r10d,r9d
   4003b:	xor    r10d,ebx
   4003e:	mov    ebp,r12d
   40041:	rol    ebp,0x1e
   40044:	add    r10d,ecx
   40047:	mov    ecx,r12d
   4004a:	rol    ecx,0x13
   4004d:	add    r10d,eax
   40050:	add    r10d,0x923f82a4
   40057:	mov    r14d,r12d
   4005a:	rol    r14d,0xa
   4005e:	xor    ecx,ebp
   40060:	xor    r14d,ecx
   40063:	mov    ecx,r8d
   40066:	xor    ecx,r15d
   40069:	and    ecx,r12d
   4006c:	mov    eax,r8d
   4006f:	and    eax,r15d
   40072:	xor    eax,ecx
   40074:	add    r11d,r10d
   40077:	mov    ecx,r11d
   4007a:	rol    ecx,0x1a
   4007d:	add    eax,r14d
   40080:	mov    ebp,r11d
   40083:	rol    ebp,0x15
   40086:	add    eax,r10d
   40089:	mov    r10d,r11d
   4008c:	rol    r10d,0x7
   40090:	xor    ebp,ecx
   40092:	xor    r10d,ebp
   40095:	mov    ecx,DWORD PTR [r13+0x1c]
   40099:	bswap  ecx
   4009b:	mov    QWORD PTR [rsp+0xb0],rcx
   400a3:	add    ecx,ebx
   400a5:	mov    ebx,r9d
   400a8:	xor    ebx,edi
   400aa:	and    ebx,r11d
   400ad:	xor    ebx,edi
   400af:	mov    ebp,eax
   400b1:	rol    ebp,0x1e
   400b4:	add    ebx,ecx
   400b6:	mov    r14d,eax
   400b9:	rol    r14d,0x13
   400bd:	lea    ecx,[r10+rbx*1]
   400c1:	add    ecx,0xab1c5ed5
   400c7:	mov    r10d,eax
   400ca:	rol    r10d,0xa
   400ce:	xor    r14d,ebp
   400d1:	xor    r10d,r14d
   400d4:	mov    ebp,r12d
   400d7:	and    ebp,r8d
   400da:	mov    esi,r12d
   400dd:	xor    esi,r8d
   400e0:	and    esi,eax
   400e2:	xor    esi,ebp
   400e4:	add    r15d,ecx
   400e7:	mov    ebp,r15d
   400ea:	rol    ebp,0x1a
   400ed:	add    esi,r10d
   400f0:	mov    r10d,r15d
   400f3:	rol    r10d,0x15
   400f7:	add    esi,ecx
   400f9:	mov    ecx,r15d
   400fc:	rol    ecx,0x7
   400ff:	xor    r10d,ebp
   40102:	xor    ecx,r10d
   40105:	mov    rbx,r13
   40108:	mov    edx,DWORD PTR [r13+0x20]
   4010c:	bswap  edx
   4010e:	mov    DWORD PTR [rsp+0xa8],edx
   40115:	add    edi,edx
   40117:	mov    r10d,r11d
   4011a:	xor    r10d,r9d
   4011d:	and    r10d,r15d
   40120:	xor    r10d,r9d
   40123:	mov    ebp,esi
   40125:	rol    ebp,0x1e
   40128:	add    r10d,edi
   4012b:	mov    edi,esi
   4012d:	rol    edi,0x13
   40130:	add    ecx,r10d
   40133:	add    ecx,0xd807aa98
   40139:	mov    r14d,esi
   4013c:	rol    r14d,0xa
   40140:	xor    edi,ebp
   40142:	xor    r14d,edi
   40145:	mov    edi,eax
   40147:	xor    edi,r12d
   4014a:	and    edi,esi
   4014c:	mov    r13d,eax
   4014f:	and    r13d,r12d
   40152:	xor    r13d,edi
   40155:	add    r8d,ecx
   40158:	mov    edi,r8d
   4015b:	rol    edi,0x1a
   4015e:	add    r13d,r14d
   40161:	mov    ebp,r8d
   40164:	rol    ebp,0x15
   40167:	add    r13d,ecx
   4016a:	mov    ecx,r8d
   4016d:	rol    ecx,0x7
   40170:	xor    ebp,edi
   40172:	xor    ecx,ebp
   40174:	mov    r10,rbx
   40177:	mov    edx,DWORD PTR [rbx+0x24]
   4017a:	bswap  edx
   4017c:	mov    QWORD PTR [rsp+0x20],rdx
   40181:	lea    edi,[rdx+r9*1]
   40185:	mov    r9d,r15d
   40188:	xor    r9d,r11d
   4018b:	and    r9d,r8d
   4018e:	xor    r9d,r11d
   40191:	mov    ebp,r13d
   40194:	rol    ebp,0x1e
   40197:	add    r9d,edi
   4019a:	mov    edi,r13d
   4019d:	rol    edi,0x13
   401a0:	add    r9d,ecx
   401a3:	add    r9d,0x12835b01
   401aa:	mov    r14d,r13d
   401ad:	rol    r14d,0xa
   401b1:	xor    edi,ebp
   401b3:	xor    r14d,edi
   401b6:	mov    edi,esi
   401b8:	and    edi,eax
   401ba:	mov    ebx,esi
   401bc:	xor    ebx,eax
   401be:	and    ebx,r13d
   401c1:	xor    ebx,edi
   401c3:	add    r12d,r9d
   401c6:	mov    edi,r12d
   401c9:	rol    edi,0x1a
   401cc:	add    ebx,r14d
   401cf:	mov    ebp,r12d
   401d2:	rol    ebp,0x15
   401d5:	add    ebx,r9d
   401d8:	mov    r9d,r12d
   401db:	rol    r9d,0x7
   401df:	xor    ebp,edi
   401e1:	xor    r9d,ebp
   401e4:	mov    ecx,DWORD PTR [r10+0x28]
   401e8:	mov    rdx,r10
   401eb:	bswap  ecx
   401ed:	mov    QWORD PTR [rsp+0x8],rcx
   401f2:	lea    edi,[rcx+r11*1]
   401f6:	mov    r11d,r8d
   401f9:	xor    r11d,r15d
   401fc:	and    r11d,r12d
   401ff:	xor    r11d,r15d
   40202:	mov    ebp,ebx
   40204:	rol    ebp,0x1e
   40207:	add    r11d,edi
   4020a:	mov    edi,ebx
   4020c:	rol    edi,0x13
   4020f:	add    r9d,r11d
   40212:	add    r9d,0x243185be
   40219:	mov    r11d,ebx
   4021c:	rol    r11d,0xa
   40220:	xor    edi,ebp
   40222:	xor    r11d,edi
   40225:	mov    edi,r13d
   40228:	xor    edi,esi
   4022a:	and    edi,ebx
   4022c:	mov    r14d,r13d
   4022f:	and    r14d,esi
   40232:	xor    r14d,edi
   40235:	add    eax,r9d
   40238:	mov    edi,eax
   4023a:	rol    edi,0x1a
   4023d:	add    r14d,r11d
   40240:	mov    r11d,eax
   40243:	rol    r11d,0x15
   40247:	add    r14d,r9d
   4024a:	mov    r9d,eax
   4024d:	rol    r9d,0x7
   40251:	xor    r11d,edi
   40254:	xor    r9d,r11d
   40257:	mov    ecx,DWORD PTR [r10+0x2c]
   4025b:	bswap  ecx
   4025d:	mov    QWORD PTR [rsp+0x18],rcx
   40262:	lea    edi,[rcx+r15*1]
   40266:	mov    r11d,r12d
   40269:	xor    r11d,r8d
   4026c:	and    r11d,eax
   4026f:	xor    r11d,r8d
   40272:	mov    ebp,r14d
   40275:	rol    ebp,0x1e
   40278:	add    r11d,edi
   4027b:	mov    r15d,r14d
   4027e:	rol    r15d,0x13
   40282:	lea    edi,[r9+r11*1]
   40286:	add    edi,0x550c7dc3
   4028c:	mov    r9d,r14d
   4028f:	rol    r9d,0xa
   40293:	xor    r15d,ebp
   40296:	xor    r9d,r15d
   40299:	mov    r11d,ebx
   4029c:	and    r11d,r13d
   4029f:	mov    r10d,ebx
   402a2:	xor    r10d,r13d
   402a5:	and    r10d,r14d
   402a8:	xor    r10d,r11d
   402ab:	add    esi,edi
   402ad:	mov    r11d,esi
   402b0:	rol    r11d,0x1a
   402b4:	add    r10d,r9d
   402b7:	mov    r9d,esi
   402ba:	rol    r9d,0x15
   402be:	add    r10d,edi
   402c1:	mov    edi,esi
   402c3:	rol    edi,0x7
   402c6:	xor    r9d,r11d
   402c9:	xor    edi,r9d
   402cc:	mov    QWORD PTR [rsp+0x100],rdx
   402d4:	mov    ecx,DWORD PTR [rdx+0x30]
   402d7:	bswap  ecx
   402d9:	mov    DWORD PTR [rsp],ecx
   402dc:	add    r8d,ecx
   402df:	mov    r9d,eax
   402e2:	xor    r9d,r12d
   402e5:	and    r9d,esi
   402e8:	xor    r9d,r12d
   402eb:	mov    r11d,r10d
   402ee:	rol    r11d,0x1e
   402f2:	add    r9d,r8d
   402f5:	mov    r8d,r10d
   402f8:	rol    r8d,0x13
   402fc:	add    edi,r9d
   402ff:	add    edi,0x72be5d74
   40305:	mov    r9d,r10d
   40308:	rol    r9d,0xa
   4030c:	xor    r8d,r11d
   4030f:	xor    r9d,r8d
   40312:	mov    r8d,r14d
   40315:	xor    r8d,ebx
   40318:	and    r8d,r10d
   4031b:	mov    ecx,r14d
   4031e:	and    ecx,ebx
   40320:	xor    ecx,r8d
   40323:	add    r13d,edi
   40326:	mov    r8d,r13d
   40329:	rol    r8d,0x1a
   4032d:	add    ecx,r9d
   40330:	mov    r9d,r13d
   40333:	rol    r9d,0x15
   40337:	add    ecx,edi
   40339:	mov    edi,r13d
   4033c:	rol    edi,0x7
   4033f:	xor    r9d,r8d
   40342:	xor    edi,r9d
   40345:	mov    edx,DWORD PTR [rdx+0x34]
   40348:	bswap  edx
   4034a:	mov    QWORD PTR [rsp+0x40],rdx
   4034f:	lea    r8d,[rdx+r12*1]
   40353:	mov    r9d,esi
   40356:	xor    r9d,eax
   40359:	and    r9d,r13d
   4035c:	xor    r9d,eax
   4035f:	mov    r11d,ecx
   40362:	rol    r11d,0x1e
   40366:	add    r9d,r8d
   40369:	mov    r8d,ecx
   4036c:	rol    r8d,0x13
   40370:	add    edi,r9d
   40373:	add    edi,0x80deb1fe
   40379:	mov    r15d,ecx
   4037c:	rol    r15d,0xa
   40380:	xor    r8d,r11d
   40383:	xor    r15d,r8d
   40386:	mov    r8d,r10d
   40389:	and    r8d,r14d
   4038c:	mov    ebp,r10d
   4038f:	xor    ebp,r14d
   40392:	and    ebp,ecx
   40394:	xor    ebp,r8d
   40397:	add    ebx,edi
   40399:	mov    r8d,ebx
   4039c:	rol    r8d,0x1a
   403a0:	add    ebp,r15d
   403a3:	mov    r11d,ebx
   403a6:	rol    r11d,0x15
   403aa:	add    ebp,edi
   403ac:	mov    edi,ebx
   403ae:	rol    edi,0x7
   403b1:	xor    r11d,r8d
   403b4:	xor    edi,r11d
   403b7:	mov    rdx,QWORD PTR [rsp+0x100]
   403bf:	mov    r8d,DWORD PTR [rdx+0x38]
   403c3:	bswap  r8d
   403c6:	mov    QWORD PTR [rsp+0x28],r8
   403cb:	add    eax,r8d
   403ce:	mov    r8d,r13d
   403d1:	xor    r8d,esi
   403d4:	and    r8d,ebx
   403d7:	mov    QWORD PTR [rsp+0x70],rbx
   403dc:	xor    r8d,esi
   403df:	mov    r11d,ebp
   403e2:	rol    r11d,0x1e
   403e6:	add    r8d,eax
   403e9:	mov    eax,ebp
   403eb:	rol    eax,0x13
   403ee:	add    edi,r8d
   403f1:	add    edi,0x9bdc06a7
   403f7:	mov    r8d,ebp
   403fa:	rol    r8d,0xa
   403fe:	xor    eax,r11d
   40401:	xor    r8d,eax
   40404:	mov    eax,ecx
   40406:	xor    eax,r10d
   40409:	and    eax,ebp
   4040b:	mov    r9d,ecx
   4040e:	and    r9d,r10d
   40411:	xor    r9d,eax
   40414:	add    r14d,edi
   40417:	mov    eax,r14d
   4041a:	rol    eax,0x1a
   4041d:	add    r9d,r8d
   40420:	mov    r8d,r14d
   40423:	rol    r8d,0x15
   40427:	add    r9d,edi
   4042a:	mov    edi,r14d
   4042d:	rol    edi,0x7
   40430:	xor    r8d,eax
   40433:	xor    edi,r8d
   40436:	mov    r11d,DWORD PTR [rdx+0x3c]
   4043a:	bswap  r11d
   4043d:	lea    eax,[r11+rsi*1]
   40441:	mov    r8d,ebx
   40444:	xor    r8d,r13d
   40447:	and    r8d,r14d
   4044a:	xor    r8d,r13d
   4044d:	mov    ebx,r9d
   40450:	rol    ebx,0x1e
   40453:	add    r8d,eax
   40456:	mov    eax,r9d
   40459:	rol    eax,0x13
   4045c:	add    r8d,edi
   4045f:	add    r8d,0xc19bf174
   40466:	mov    r15d,r9d
   40469:	rol    r15d,0xa
   4046d:	xor    eax,ebx
   4046f:	xor    r15d,eax
   40472:	mov    eax,ebp
   40474:	mov    DWORD PTR [rsp+0x98],ecx
   4047b:	and    eax,ecx
   4047d:	mov    edx,ebp
   4047f:	xor    edx,ecx
   40481:	and    edx,r9d
   40484:	xor    edx,eax
   40486:	add    edx,r15d
   40489:	mov    rcx,rdx
   4048c:	mov    edx,DWORD PTR [rsp+0x58]
   40490:	mov    eax,edx
   40492:	rol    eax,0x19
   40495:	add    ecx,r8d
   40498:	mov    QWORD PTR [rsp+0x10],rcx
   4049d:	mov    rdi,QWORD PTR [rsp+0x78]
   404a2:	mov    ebx,edi
   404a4:	rol    ebx,0x19
   404a7:	add    r10d,r8d
   404aa:	mov    r8d,edx
   404ad:	mov    ecx,edx
   404af:	rol    r8d,0xe
   404b3:	xor    r8d,eax
   404b6:	mov    eax,edi
   404b8:	rol    eax,0xe
   404bb:	xor    eax,ebx
   404bd:	mov    rsi,QWORD PTR [rsp+0x88]
   404c5:	mov    ebx,esi
   404c7:	rol    ebx,0x19
   404ca:	mov    r15d,esi
   404cd:	rol    r15d,0xe
   404d1:	xor    r15d,ebx
   404d4:	mov    rdx,QWORD PTR [rsp+0x60]
   404d9:	mov    ebx,edx
   404db:	rol    ebx,0x19
   404de:	mov    r12d,edx
   404e1:	rol    r12d,0xe
   404e5:	xor    r12d,ebx
   404e8:	mov    ebx,ecx
   404ea:	shr    ebx,0x3
   404ed:	xor    ebx,r8d
   404f0:	mov    r8d,edi
   404f3:	shr    r8d,0x3
   404f7:	xor    r8d,eax
   404fa:	mov    eax,esi
   404fc:	shr    eax,0x3
   404ff:	xor    eax,r15d
   40502:	mov    r15d,edx
   40505:	shr    r15d,0x3
   40509:	xor    r15d,r12d
   4050c:	add    edi,DWORD PTR [rsp]
   4050f:	add    edi,ebx
   40511:	add    esi,DWORD PTR [rsp+0x18]
   40515:	add    esi,r8d
   40518:	mov    rcx,rsi
   4051b:	add    edx,DWORD PTR [rsp+0x8]
   4051f:	add    edx,eax
   40521:	mov    r12,rdx
   40524:	mov    rsi,QWORD PTR [rsp+0x28]
   40529:	mov    eax,esi
   4052b:	rol    eax,0xf
   4052e:	mov    rdx,QWORD PTR [rsp+0x48]
   40533:	add    edx,DWORD PTR [rsp+0x20]
   40537:	mov    r8d,esi
   4053a:	rol    r8d,0xd
   4053e:	add    edx,r15d
   40541:	mov    r15,rdx
   40544:	xor    r8d,eax
   40547:	mov    edx,esi
   40549:	shr    edx,0xa
   4054c:	xor    edx,r8d
   4054f:	mov    QWORD PTR [rsp+0x80],r11
   40557:	mov    eax,r11d
   4055a:	rol    eax,0xf
   4055d:	add    edx,r15d
   40560:	mov    r8d,r11d
   40563:	rol    r8d,0xd
   40567:	xor    r8d,eax
   4056a:	shr    r11d,0xa
   4056e:	xor    r11d,r8d
   40571:	add    r11d,r12d
   40574:	mov    eax,edx
   40576:	rol    eax,0xf
   40579:	mov    r8d,edx
   4057c:	rol    r8d,0xd
   40580:	xor    r8d,eax
   40583:	mov    eax,edx
   40585:	mov    ebx,edx
   40587:	mov    DWORD PTR [rsp+0x78],edx
   4058b:	shr    eax,0xa
   4058e:	xor    eax,r8d
   40591:	add    eax,ecx
   40593:	mov    r15,rax
   40596:	mov    QWORD PTR [rsp+0x48],rax
   4059b:	mov    eax,r11d
   4059e:	rol    eax,0xf
   405a1:	mov    edx,r11d
   405a4:	rol    edx,0xd
   405a7:	xor    edx,eax
   405a9:	mov    eax,r11d
   405ac:	mov    r8,r11
   405af:	mov    QWORD PTR [rsp+0x88],r11
   405b7:	shr    eax,0xa
   405ba:	mov    rcx,rax
   405bd:	mov    eax,r10d
   405c0:	rol    eax,0x1a
   405c3:	xor    ecx,edx
   405c5:	mov    edx,r10d
   405c8:	rol    edx,0x15
   405cb:	add    ecx,edi
   405cd:	mov    r12,rcx
   405d0:	mov    QWORD PTR [rsp+0x60],rcx
   405d5:	mov    esi,r10d
   405d8:	rol    esi,0x7
   405db:	xor    edx,eax
   405dd:	xor    esi,edx
   405df:	add    r13d,ebx
   405e2:	mov    eax,r14d
   405e5:	mov    r11,QWORD PTR [rsp+0x70]
   405ea:	xor    eax,r11d
   405ed:	and    eax,r10d
   405f0:	xor    eax,r11d
   405f3:	add    eax,r13d
   405f6:	add    eax,esi
   405f8:	add    eax,0xe49b69c1
   405fd:	mov    rdi,QWORD PTR [rsp+0x10]
   40602:	mov    edx,edi
   40604:	rol    edx,0x1e
   40607:	mov    esi,edi
   40609:	rol    esi,0x13
   4060c:	xor    esi,edx
   4060e:	mov    edx,edi
   40610:	rol    edx,0xa
   40613:	xor    edx,esi
   40615:	mov    esi,r9d
   40618:	xor    esi,ebp
   4061a:	and    esi,edi
   4061c:	mov    ecx,r9d
   4061f:	and    ecx,ebp
   40621:	xor    ecx,esi
   40623:	add    ecx,edx
   40625:	add    ecx,eax
   40627:	mov    esi,ecx
   40629:	mov    r13d,DWORD PTR [rsp+0x98]
   40631:	add    r13d,eax
   40634:	mov    eax,r13d
   40637:	rol    eax,0x1a
   4063a:	mov    edx,r13d
   4063d:	rol    edx,0x15
   40640:	xor    edx,eax
   40642:	mov    eax,r13d
   40645:	rol    eax,0x7
   40648:	xor    eax,edx
   4064a:	lea    ecx,[r8+r11*1]
   4064e:	mov    edx,r10d
   40651:	xor    edx,r14d
   40654:	and    edx,r13d
   40657:	xor    edx,r14d
   4065a:	mov    r8d,esi
   4065d:	rol    esi,0x1e
   40660:	add    edx,ecx
   40662:	mov    ecx,r8d
   40665:	rol    ecx,0x13
   40668:	add    eax,edx
   4066a:	add    eax,0xefbe4786
   4066f:	mov    edx,r8d
   40672:	mov    r11d,r8d
   40675:	rol    edx,0xa
   40678:	xor    ecx,esi
   4067a:	xor    edx,ecx
   4067c:	mov    ecx,edi
   4067e:	and    ecx,r9d
   40681:	mov    ebx,edi
   40683:	xor    ebx,r9d
   40686:	and    ebx,r8d
   40689:	xor    ebx,ecx
   4068b:	add    ebp,eax
   4068d:	mov    ecx,ebp
   4068f:	rol    ecx,0x1a
   40692:	add    ebx,edx
   40694:	mov    edx,ebp
   40696:	rol    edx,0x15
   40699:	add    ebx,eax
   4069b:	mov    eax,ebp
   4069d:	rol    eax,0x7
   406a0:	xor    edx,ecx
   406a2:	xor    eax,edx
   406a4:	lea    ecx,[r15+r14*1]
   406a8:	mov    edx,r13d
   406ab:	xor    edx,r10d
   406ae:	and    edx,ebp
   406b0:	mov    QWORD PTR [rsp+0x68],rbp
   406b5:	xor    edx,r10d
   406b8:	add    edx,ecx
   406ba:	add    eax,edx
   406bc:	add    eax,0xfc19dc6
   406c1:	mov    ecx,ebx
   406c3:	rol    ecx,0x1e
   406c6:	mov    edx,ebx
   406c8:	rol    edx,0x13
   406cb:	xor    edx,ecx
   406cd:	mov    ecx,ebx
   406cf:	rol    ecx,0xa
   406d2:	xor    ecx,edx
   406d4:	mov    edx,r8d
   406d7:	xor    edx,edi
   406d9:	and    edx,ebx
   406db:	mov    esi,r8d
   406de:	and    esi,edi
   406e0:	xor    esi,edx
   406e2:	add    esi,ecx
   406e4:	add    esi,eax
   406e6:	add    r9d,eax
   406e9:	mov    eax,r9d
   406ec:	rol    eax,0x1a
   406ef:	mov    ecx,r9d
   406f2:	rol    ecx,0x15
   406f5:	xor    ecx,eax
   406f7:	mov    eax,r9d
   406fa:	mov    QWORD PTR [rsp+0xc0],r9
   40702:	rol    eax,0x7
   40705:	xor    eax,ecx
   40707:	lea    ecx,[r12+r10*1]
   4070b:	mov    edx,ebp
   4070d:	mov    DWORD PTR [rsp+0x98],r13d
   40715:	xor    edx,r13d
   40718:	and    edx,r9d
   4071b:	xor    edx,r13d
   4071e:	mov    r8d,esi
   40721:	rol    r8d,0x1e
   40725:	add    edx,ecx
   40727:	mov    ecx,esi
   40729:	rol    ecx,0x13
   4072c:	lea    ebp,[rax+rdx*1]
   4072f:	add    ebp,0x240ca1cc
   40735:	mov    r14d,esi
   40738:	mov    rdi,rsi
   4073b:	mov    QWORD PTR [rsp+0xa0],rsi
   40743:	rol    r14d,0xa
   40747:	xor    ecx,r8d
   4074a:	mov    esi,DWORD PTR [rsp+0xa8]
   40751:	mov    edx,esi
   40753:	rol    edx,0x19
   40756:	xor    r14d,ecx
   40759:	mov    rcx,QWORD PTR [rsp+0xb0]
   40761:	mov    r12d,ecx
   40764:	rol    r12d,0x19
   40768:	mov    rax,QWORD PTR [rsp+0x38]
   4076d:	mov    r8d,eax
   40770:	rol    r8d,0x19
   40774:	mov    DWORD PTR [rsp+0x94],r8d
   4077c:	mov    r15d,ebx
   4077f:	mov    DWORD PTR [rsp+0xc8],r11d
   40787:	and    r15d,r11d
   4078a:	mov    r8,QWORD PTR [rsp+0x50]
   4078f:	mov    r9d,r8d
   40792:	rol    r9d,0x19
   40796:	mov    DWORD PTR [rsp+0xb8],r9d
   4079e:	mov    r9d,esi
   407a1:	rol    r9d,0xe
   407a5:	mov    r13d,ebx
   407a8:	xor    r13d,r11d
   407ab:	mov    esi,ecx
   407ad:	rol    esi,0xe
   407b0:	mov    r10d,esi
   407b3:	and    r13d,edi
   407b6:	mov    ecx,eax
   407b8:	rol    ecx,0xe
   407bb:	mov    DWORD PTR [rsp+0x70],ecx
   407bf:	xor    r13d,r15d
   407c2:	mov    eax,r8d
   407c5:	rol    eax,0xe
   407c8:	mov    DWORD PTR [rsp+0x34],eax
   407cc:	add    r13d,r14d
   407cf:	mov    eax,DWORD PTR [rsp]
   407d2:	mov    esi,eax
   407d4:	rol    esi,0x19
   407d7:	add    r13d,ebp
   407da:	mov    rdi,QWORD PTR [rsp+0x18]
   407df:	mov    ecx,edi
   407e1:	rol    ecx,0x19
   407e4:	mov    r8,QWORD PTR [rsp+0x10]
   407e9:	add    r8d,ebp
   407ec:	mov    QWORD PTR [rsp+0x10],r8
   407f1:	mov    r11,QWORD PTR [rsp+0x8]
   407f6:	mov    ebp,r11d
   407f9:	rol    ebp,0x19
   407fc:	xor    r9d,edx
   407ff:	mov    DWORD PTR [rsp+0xf0],r9d
   40807:	mov    rdx,QWORD PTR [rsp+0x20]
   4080c:	mov    r15d,edx
   4080f:	rol    r15d,0x19
   40813:	xor    r10d,r12d
   40816:	mov    DWORD PTR [rsp+0xfc],r10d
   4081e:	rol    eax,0xe
   40821:	mov    r8d,eax
   40824:	mov    eax,DWORD PTR [rsp+0x94]
   4082b:	xor    DWORD PTR [rsp+0x70],eax
   4082f:	mov    eax,edi
   40831:	rol    eax,0xe
   40834:	mov    edi,DWORD PTR [rsp+0xb8]
   4083b:	xor    DWORD PTR [rsp+0x34],edi
   4083f:	mov    r12d,r11d
   40842:	rol    r12d,0xe
   40846:	xor    r8d,esi
   40849:	mov    DWORD PTR [rsp+0x94],r8d
   40851:	mov    r14d,edx
   40854:	rol    r14d,0xe
   40858:	xor    eax,ecx
   4085a:	mov    DWORD PTR [rsp+0xf8],eax
   40861:	mov    r11d,DWORD PTR [rsp+0x78]
   40866:	mov    ecx,r11d
   40869:	rol    ecx,0x19
   4086c:	xor    r12d,ebp
   4086f:	mov    rbp,QWORD PTR [rsp+0x80]
   40877:	mov    edx,ebp
   40879:	rol    edx,0x19
   4087c:	xor    r14d,r15d
   4087f:	mov    r15d,r11d
   40882:	rol    r15d,0xe
   40886:	xor    r15d,ecx
   40889:	mov    esi,ebp
   4088b:	rol    esi,0xe
   4088e:	xor    esi,edx
   40890:	mov    r8,QWORD PTR [rsp+0x28]
   40895:	mov    edx,r8d
   40898:	rol    edx,0x19
   4089b:	mov    edi,r8d
   4089e:	rol    edi,0xe
   408a1:	xor    edi,edx
   408a3:	mov    r9,QWORD PTR [rsp+0x40]
   408a8:	mov    edx,r9d
   408ab:	rol    edx,0x19
   408ae:	mov    r10d,r9d
   408b1:	rol    r10d,0xe
   408b5:	xor    r10d,edx
   408b8:	mov    ecx,r11d
   408bb:	shr    ecx,0x3
   408be:	xor    ecx,r15d
   408c1:	mov    rdx,QWORD PTR [rsp+0x38]
   408c6:	mov    r15d,edx
   408c9:	add    edx,ebp
   408cb:	mov    rax,rbp
   408ce:	add    ecx,eax
   408d0:	mov    DWORD PTR [rsp+0xb8],ecx
   408d7:	shr    eax,0x3
   408da:	xor    eax,esi
   408dc:	mov    rbp,QWORD PTR [rsp+0x50]
   408e1:	mov    ecx,ebp
   408e3:	add    ebp,r8d
   408e6:	add    eax,r8d
   408e9:	mov    QWORD PTR [rsp+0x80],rax
   408f1:	shr    r8d,0x3
   408f5:	xor    r8d,edi
   408f8:	mov    rax,r9
   408fb:	mov    r9d,DWORD PTR [rsp+0x58]
   40900:	add    r9d,eax
   40903:	add    r8d,eax
   40906:	mov    QWORD PTR [rsp+0x28],r8
   4090b:	shr    eax,0x3
   4090e:	xor    eax,r10d
   40911:	mov    r8d,DWORD PTR [rsp]
   40915:	add    eax,r8d
   40918:	mov    QWORD PTR [rsp+0x40],rax
   4091d:	shr    r8d,0x3
   40921:	xor    r8d,DWORD PTR [rsp+0x94]
   40929:	mov    rax,QWORD PTR [rsp+0x18]
   4092e:	add    r8d,eax
   40931:	mov    DWORD PTR [rsp+0x94],r8d
   40939:	shr    eax,0x3
   4093c:	xor    eax,DWORD PTR [rsp+0xf8]
   40943:	mov    rsi,QWORD PTR [rsp+0x8]
   40948:	add    eax,esi
   4094a:	mov    QWORD PTR [rsp+0x18],rax
   4094f:	shr    esi,0x3
   40952:	xor    esi,r12d
   40955:	mov    rax,QWORD PTR [rsp+0x20]
   4095a:	add    esi,eax
   4095c:	mov    QWORD PTR [rsp+0x8],rsi
   40961:	shr    eax,0x3
   40964:	xor    eax,r14d
   40967:	mov    esi,DWORD PTR [rsp+0xa8]
   4096e:	add    eax,esi
   40970:	mov    QWORD PTR [rsp+0x20],rax
   40975:	mov    eax,esi
   40977:	shr    eax,0x3
   4097a:	xor    eax,DWORD PTR [rsp+0xf0]
   40981:	mov    rsi,QWORD PTR [rsp+0xb0]
   40989:	add    eax,esi
   4098b:	shr    esi,0x3
   4098e:	xor    esi,DWORD PTR [rsp+0xfc]
   40995:	shr    r15d,0x3
   40999:	xor    r15d,DWORD PTR [rsp+0x70]
   4099e:	shr    ecx,0x3
   409a1:	xor    ecx,DWORD PTR [rsp+0x34]
   409a5:	add    edx,esi
   409a7:	mov    r8,QWORD PTR [rsp+0x48]
   409ac:	mov    esi,r8d
   409af:	rol    esi,0xf
   409b2:	add    ebp,r15d
   409b5:	mov    r14d,r8d
   409b8:	rol    r14d,0xd
   409bc:	mov    edi,r9d
   409bf:	add    edi,ecx
   409c1:	xor    r14d,esi
   409c4:	mov    r9d,r8d
   409c7:	shr    r9d,0xa
   409cb:	xor    r9d,r14d
   409ce:	mov    r8,QWORD PTR [rsp+0x60]
   409d3:	mov    ecx,r8d
   409d6:	rol    ecx,0xf
   409d9:	add    r9d,edi
   409dc:	mov    esi,r8d
   409df:	rol    esi,0xd
   409e2:	xor    esi,ecx
   409e4:	mov    edi,r8d
   409e7:	shr    edi,0xa
   409ea:	xor    edi,esi
   409ec:	add    edi,ebp
   409ee:	mov    ecx,r9d
   409f1:	rol    ecx,0xf
   409f4:	mov    esi,r9d
   409f7:	rol    esi,0xd
   409fa:	xor    esi,ecx
   409fc:	mov    ecx,r9d
   409ff:	mov    DWORD PTR [rsp+0x38],r9d
   40a04:	shr    ecx,0xa
   40a07:	xor    ecx,esi
   40a09:	add    ecx,edx
   40a0b:	mov    r12,rcx
   40a0e:	mov    ecx,edi
   40a10:	rol    ecx,0xf
   40a13:	mov    esi,edi
   40a15:	rol    esi,0xd
   40a18:	xor    esi,ecx
   40a1a:	mov    ecx,edi
   40a1c:	mov    QWORD PTR [rsp],rdi
   40a20:	shr    ecx,0xa
   40a23:	xor    ecx,esi
   40a25:	add    eax,r11d
   40a28:	add    ecx,eax
   40a2a:	mov    r10,rcx
   40a2d:	mov    rdx,QWORD PTR [rsp+0x10]
   40a32:	mov    eax,edx
   40a34:	rol    eax,0x1a
   40a37:	mov    ecx,edx
   40a39:	rol    ecx,0x15
   40a3c:	xor    ecx,eax
   40a3e:	mov    eax,edx
   40a40:	rol    eax,0x7
   40a43:	xor    eax,ecx
   40a45:	mov    r8d,DWORD PTR [rsp+0x98]
   40a4d:	add    r8d,r9d
   40a50:	mov    r15,QWORD PTR [rsp+0xc0]
   40a58:	mov    ecx,r15d
   40a5b:	mov    rsi,QWORD PTR [rsp+0x68]
   40a60:	xor    ecx,esi
   40a62:	and    ecx,edx
   40a64:	xor    ecx,esi
   40a66:	mov    r9,rsi
   40a69:	add    ecx,r8d
   40a6c:	mov    r8,r13
   40a6f:	mov    esi,r8d
   40a72:	rol    esi,0x1e
   40a75:	add    ecx,eax
   40a77:	add    ecx,0x2de92c6f
   40a7d:	mov    eax,r8d
   40a80:	rol    eax,0x13
   40a83:	xor    eax,esi
   40a85:	mov    esi,r8d
   40a88:	rol    esi,0xa
   40a8b:	xor    esi,eax
   40a8d:	mov    rbp,QWORD PTR [rsp+0xa0]
   40a95:	mov    r14d,ebp
   40a98:	xor    r14d,ebx
   40a9b:	and    r14d,r8d
   40a9e:	mov    eax,ebp
   40aa0:	and    eax,ebx
   40aa2:	xor    eax,r14d
   40aa5:	add    eax,esi
   40aa7:	mov    r11d,DWORD PTR [rsp+0xc8]
   40aaf:	add    r11d,ecx
   40ab2:	mov    esi,r11d
   40ab5:	rol    esi,0x1a
   40ab8:	add    eax,ecx
   40aba:	mov    ecx,r11d
   40abd:	rol    ecx,0x15
   40ac0:	xor    ecx,esi
   40ac2:	mov    esi,r11d
   40ac5:	rol    esi,0x7
   40ac8:	xor    esi,ecx
   40aca:	lea    ecx,[rdi+r9*1]
   40ace:	mov    r9d,edx
   40ad1:	mov    rdi,r15
   40ad4:	xor    r9d,edi
   40ad7:	and    r9d,r11d
   40ada:	xor    r9d,edi
   40add:	add    r9d,ecx
   40ae0:	add    esi,r9d
   40ae3:	add    esi,0x4a7484aa
   40ae9:	mov    ecx,eax
   40aeb:	rol    ecx,0x1e
   40aee:	mov    r9d,eax
   40af1:	rol    r9d,0x13
   40af5:	xor    r9d,ecx
   40af8:	mov    r14d,eax
   40afb:	rol    r14d,0xa
   40aff:	xor    r14d,r9d
   40b02:	mov    r9d,r8d
   40b05:	and    r9d,ebp
   40b08:	mov    ecx,r8d
   40b0b:	xor    ecx,ebp
   40b0d:	and    ecx,eax
   40b0f:	xor    ecx,r9d
   40b12:	add    ecx,r14d
   40b15:	add    ecx,esi
   40b17:	mov    r15,rbx
   40b1a:	add    r15d,esi
   40b1d:	mov    esi,r15d
   40b20:	rol    esi,0x1a
   40b23:	mov    r9d,r15d
   40b26:	rol    r9d,0x15
   40b2a:	xor    r9d,esi
   40b2d:	mov    esi,r15d
   40b30:	rol    esi,0x7
   40b33:	xor    esi,r9d
   40b36:	mov    r14d,r11d
   40b39:	xor    r14d,edx
   40b3c:	and    r14d,r15d
   40b3f:	xor    r14d,edx
   40b42:	add    r14d,r12d
   40b45:	add    r14d,edi
   40b48:	mov    r9d,ecx
   40b4b:	rol    r9d,0x1e
   40b4f:	add    esi,r14d
   40b52:	add    esi,0x5cb0a9dc
   40b58:	mov    r14d,ecx
   40b5b:	rol    r14d,0x13
   40b5f:	xor    r14d,r9d
   40b62:	mov    r13d,ecx
   40b65:	rol    r13d,0xa
   40b69:	xor    r13d,r14d
   40b6c:	mov    r14d,eax
   40b6f:	xor    r14d,r8d
   40b72:	and    r14d,ecx
   40b75:	mov    r9d,eax
   40b78:	and    r9d,r8d
   40b7b:	xor    r9d,r14d
   40b7e:	add    r9d,r13d
   40b81:	mov    rbx,rbp
   40b84:	add    ebx,esi
   40b86:	mov    r14d,ebx
   40b89:	rol    r14d,0x1a
   40b8d:	add    r9d,esi
   40b90:	mov    esi,ebx
   40b92:	rol    esi,0x15
   40b95:	xor    esi,r14d
   40b98:	mov    r14d,ebx
   40b9b:	rol    r14d,0x7
   40b9f:	xor    r14d,esi
   40ba2:	mov    edi,r15d
   40ba5:	xor    edi,r11d
   40ba8:	and    edi,ebx
   40baa:	xor    edi,r11d
   40bad:	add    edi,r10d
   40bb0:	add    edi,edx
   40bb2:	lea    esi,[r14+rdi*1]
   40bb6:	add    esi,0x76f988da
   40bbc:	mov    edi,r9d
   40bbf:	rol    edi,0x1e
   40bc2:	mov    r14d,r9d
   40bc5:	rol    r14d,0x13
   40bc9:	xor    r14d,edi
   40bcc:	mov    r13d,r9d
   40bcf:	rol    r13d,0xa
   40bd3:	xor    r13d,r14d
   40bd6:	mov    r14d,ecx
   40bd9:	and    r14d,eax
   40bdc:	mov    edi,ecx
   40bde:	xor    edi,eax
   40be0:	and    edi,r9d
   40be3:	xor    edi,r14d
   40be6:	add    edi,r13d
   40be9:	add    edi,esi
   40beb:	add    r8d,esi
   40bee:	mov    QWORD PTR [rsp+0x58],r12
   40bf3:	mov    esi,r12d
   40bf6:	rol    esi,0xf
   40bf9:	mov    r14d,r12d
   40bfc:	rol    r14d,0xd
   40c00:	xor    r14d,esi
   40c03:	mov    ebp,r12d
   40c06:	shr    ebp,0xa
   40c09:	xor    ebp,r14d
   40c0c:	mov    rdx,QWORD PTR [rsp+0x20]
   40c11:	add    edx,DWORD PTR [rsp+0x88]
   40c18:	add    ebp,edx
   40c1a:	mov    rdx,r10
   40c1d:	mov    QWORD PTR [rsp+0x50],r10
   40c22:	mov    esi,edx
   40c24:	rol    esi,0xf
   40c27:	mov    r14d,edx
   40c2a:	rol    r14d,0xd
   40c2e:	xor    r14d,esi
   40c31:	shr    edx,0xa
   40c34:	xor    edx,r14d
   40c37:	mov    rsi,QWORD PTR [rsp+0x8]
   40c3c:	add    esi,DWORD PTR [rsp+0x48]
   40c40:	add    edx,esi
   40c42:	mov    esi,ebp
   40c44:	rol    esi,0xf
   40c47:	mov    r14d,ebp
   40c4a:	rol    r14d,0xd
   40c4e:	xor    r14d,esi
   40c51:	mov    esi,ebp
   40c53:	shr    esi,0xa
   40c56:	xor    esi,r14d
   40c59:	mov    r10,QWORD PTR [rsp+0x18]
   40c5e:	add    r10d,DWORD PTR [rsp+0x60]
   40c63:	add    esi,r10d
   40c66:	mov    r12,rsi
   40c69:	mov    esi,edx
   40c6b:	rol    esi,0xf
   40c6e:	mov    r14d,edx
   40c71:	rol    r14d,0xd
   40c75:	xor    r14d,esi
   40c78:	mov    r13d,edx
   40c7b:	mov    r10,rdx
   40c7e:	mov    QWORD PTR [rsp+0x98],rdx
   40c86:	shr    r13d,0xa
   40c8a:	xor    r13d,r14d
   40c8d:	mov    edx,DWORD PTR [rsp+0x94]
   40c94:	add    edx,DWORD PTR [rsp+0x38]
   40c98:	add    r13d,edx
   40c9b:	mov    edx,r8d
   40c9e:	rol    edx,0x1a
   40ca1:	mov    esi,r8d
   40ca4:	rol    esi,0x15
   40ca7:	xor    esi,edx
   40ca9:	mov    edx,r8d
   40cac:	rol    edx,0x7
   40caf:	xor    edx,esi
   40cb1:	add    r11d,ebp
   40cb4:	mov    DWORD PTR [rsp+0x34],ebp
   40cb8:	mov    esi,ebx
   40cba:	xor    esi,r15d
   40cbd:	and    esi,r8d
   40cc0:	xor    esi,r15d
   40cc3:	add    esi,r11d
   40cc6:	mov    r11d,edi
   40cc9:	rol    r11d,0x1e
   40ccd:	add    edx,esi
   40ccf:	add    edx,0x983e5152
   40cd5:	mov    esi,edi
   40cd7:	rol    esi,0x13
   40cda:	xor    esi,r11d
   40cdd:	mov    r14d,edi
   40ce0:	rol    r14d,0xa
   40ce4:	xor    r14d,esi
   40ce7:	mov    esi,r9d
   40cea:	xor    esi,ecx
   40cec:	and    esi,edi
   40cee:	mov    r11d,r9d
   40cf1:	and    r11d,ecx
   40cf4:	xor    r11d,esi
   40cf7:	add    r11d,r14d
   40cfa:	add    eax,edx
   40cfc:	mov    esi,eax
   40cfe:	rol    esi,0x1a
   40d01:	add    r11d,edx
   40d04:	mov    edx,eax
   40d06:	rol    edx,0x15
   40d09:	xor    edx,esi
   40d0b:	mov    esi,eax
   40d0d:	rol    esi,0x7
   40d10:	xor    esi,edx
   40d12:	lea    edx,[r10+r15*1]
   40d16:	mov    r10d,r8d
   40d19:	xor    r10d,ebx
   40d1c:	and    r10d,eax
   40d1f:	xor    r10d,ebx
   40d22:	add    r10d,edx
   40d25:	lea    edx,[rsi+r10*1]
   40d29:	add    edx,0xa831c66d
   40d2f:	mov    esi,r11d
   40d32:	rol    esi,0x1e
   40d35:	mov    r10d,r11d
   40d38:	rol    r10d,0x13
   40d3c:	xor    r10d,esi
   40d3f:	mov    r14d,r11d
   40d42:	rol    r14d,0xa
   40d46:	xor    r14d,r10d
   40d49:	mov    r10d,edi
   40d4c:	and    r10d,r9d
   40d4f:	mov    r15d,edi
   40d52:	xor    r15d,r9d
   40d55:	and    r15d,r11d
   40d58:	xor    r15d,r10d
   40d5b:	add    r15d,r14d
   40d5e:	add    r15d,edx
   40d61:	add    ecx,edx
   40d63:	mov    edx,ecx
   40d65:	rol    edx,0x1a
   40d68:	mov    r10d,ecx
   40d6b:	rol    r10d,0x15
   40d6f:	xor    r10d,edx
   40d72:	mov    edx,ecx
   40d74:	rol    edx,0x7
   40d77:	xor    edx,r10d
   40d7a:	lea    r10d,[r12+rbx*1]
   40d7e:	mov    ebx,eax
   40d80:	xor    ebx,r8d
   40d83:	and    ebx,ecx
   40d85:	xor    ebx,r8d
   40d88:	add    ebx,r10d
   40d8b:	mov    r10d,r15d
   40d8e:	rol    r10d,0x1e
   40d92:	add    edx,ebx
   40d94:	add    edx,0xb00327c8
   40d9a:	mov    ebx,r15d
   40d9d:	rol    ebx,0x13
   40da0:	xor    ebx,r10d
   40da3:	mov    r10d,r15d
   40da6:	rol    r10d,0xa
   40daa:	xor    r10d,ebx
   40dad:	mov    ebx,r11d
   40db0:	xor    ebx,edi
   40db2:	and    ebx,r15d
   40db5:	mov    r14d,r11d
   40db8:	and    r14d,edi
   40dbb:	xor    r14d,ebx
   40dbe:	add    r14d,r10d
   40dc1:	add    r9d,edx
   40dc4:	mov    r10d,r9d
   40dc7:	rol    r10d,0x1a
   40dcb:	add    r14d,edx
   40dce:	mov    edx,r9d
   40dd1:	rol    edx,0x15
   40dd4:	xor    edx,r10d
   40dd7:	mov    r10d,r9d
   40dda:	rol    r10d,0x7
   40dde:	xor    r10d,edx
   40de1:	lea    edx,[r8+r13*1]
   40de5:	mov    r8d,ecx
   40de8:	xor    r8d,eax
   40deb:	and    r8d,r9d
   40dee:	xor    r8d,eax
   40df1:	add    r8d,edx
   40df4:	lea    edx,[r10+r8*1]
   40df8:	add    edx,0xbf597fc7
   40dfe:	mov    r8d,r14d
   40e01:	rol    r8d,0x1e
   40e05:	mov    r10d,r14d
   40e08:	rol    r10d,0x13
   40e0c:	xor    r10d,r8d
   40e0f:	mov    ebx,r14d
   40e12:	rol    ebx,0xa
   40e15:	xor    ebx,r10d
   40e18:	mov    r10d,r15d
   40e1b:	and    r10d,r11d
   40e1e:	mov    esi,r15d
   40e21:	xor    esi,r11d
   40e24:	and    esi,r14d
   40e27:	xor    esi,r10d
   40e2a:	add    esi,ebx
   40e2c:	add    esi,edx
   40e2e:	mov    rbx,rsi
   40e31:	add    edi,edx
   40e33:	mov    QWORD PTR [rsp+0x18],r12
   40e38:	mov    edx,r12d
   40e3b:	rol    edx,0xf
   40e3e:	mov    r10d,r12d
   40e41:	rol    r10d,0xd
   40e45:	xor    r10d,edx
   40e48:	mov    esi,r12d
   40e4b:	shr    esi,0xa
   40e4e:	xor    esi,r10d
   40e51:	mov    rdx,QWORD PTR [rsp+0x40]
   40e56:	add    edx,DWORD PTR [rsp]
   40e59:	add    esi,edx
   40e5b:	mov    QWORD PTR [rsp+0xb0],r13
   40e63:	mov    edx,r13d
   40e66:	rol    edx,0xf
   40e69:	mov    r10d,r13d
   40e6c:	rol    r10d,0xd
   40e70:	xor    r10d,edx
   40e73:	mov    edx,r13d
   40e76:	mov    r8,rdx
   40e79:	shr    r8d,0xa
   40e7d:	xor    r8d,r10d
   40e80:	mov    rdx,QWORD PTR [rsp+0x28]
   40e85:	add    edx,DWORD PTR [rsp+0x58]
   40e89:	add    r8d,edx
   40e8c:	mov    edx,esi
   40e8e:	rol    edx,0xf
   40e91:	mov    r10d,esi
   40e94:	rol    r10d,0xd
   40e98:	xor    r10d,edx
   40e9b:	mov    r13d,esi
   40e9e:	mov    DWORD PTR [rsp+0xa8],esi
   40ea5:	shr    r13d,0xa
   40ea9:	xor    r13d,r10d
   40eac:	mov    r10,QWORD PTR [rsp+0x80]
   40eb4:	add    r10d,DWORD PTR [rsp+0x50]
   40eb9:	add    r13d,r10d
   40ebc:	mov    QWORD PTR [rsp+0x10],r13
   40ec1:	mov    edx,r8d
   40ec4:	rol    edx,0xf
   40ec7:	mov    r10d,r8d
   40eca:	rol    r10d,0xd
   40ece:	xor    r10d,edx
   40ed1:	mov    edx,r8d
   40ed4:	mov    QWORD PTR [rsp+0x40],r8
   40ed9:	shr    edx,0xa
   40edc:	xor    edx,r10d
   40edf:	mov    r10d,DWORD PTR [rsp+0xb8]
   40ee7:	add    r10d,ebp
   40eea:	add    edx,r10d
   40eed:	mov    QWORD PTR [rsp+0x8],rdx
   40ef2:	mov    edx,edi
   40ef4:	rol    edx,0x1a
   40ef7:	mov    r10d,edi
   40efa:	rol    r10d,0x15
   40efe:	xor    r10d,edx
   40f01:	mov    edx,edi
   40f03:	rol    edx,0x7
   40f06:	xor    edx,r10d
   40f09:	add    eax,esi
   40f0b:	mov    r10d,r9d
   40f0e:	xor    r10d,ecx
   40f11:	and    r10d,edi
   40f14:	xor    r10d,ecx
   40f17:	add    r10d,eax
   40f1a:	mov    eax,ebx
   40f1c:	rol    eax,0x1e
   40f1f:	add    edx,r10d
   40f22:	add    edx,0xc6e00bf3
   40f28:	mov    r10d,ebx
   40f2b:	rol    r10d,0x13
   40f2f:	xor    r10d,eax
   40f32:	mov    eax,ebx
   40f34:	mov    rsi,rbx
   40f37:	rol    eax,0xa
   40f3a:	xor    eax,r10d
   40f3d:	mov    ebx,r14d
   40f40:	xor    ebx,r15d
   40f43:	and    ebx,esi
   40f45:	mov    r12d,r14d
   40f48:	and    r12d,r15d
   40f4b:	xor    r12d,ebx
   40f4e:	add    r12d,eax
   40f51:	add    r11d,edx
   40f54:	mov    eax,r11d
   40f57:	rol    eax,0x1a
   40f5a:	add    r12d,edx
   40f5d:	mov    edx,r11d
   40f60:	rol    edx,0x15
   40f63:	xor    edx,eax
   40f65:	mov    eax,r11d
   40f68:	rol    eax,0x7
   40f6b:	xor    eax,edx
   40f6d:	add    ecx,r8d
   40f70:	mov    edx,edi
   40f72:	xor    edx,r9d
   40f75:	and    edx,r11d
   40f78:	xor    edx,r9d
   40f7b:	add    edx,ecx
   40f7d:	add    eax,edx
   40f7f:	add    eax,0xd5a79147
   40f84:	mov    ecx,r12d
   40f87:	rol    ecx,0x1e
   40f8a:	mov    edx,r12d
   40f8d:	rol    edx,0x13
   40f90:	xor    edx,ecx
   40f92:	mov    ecx,r12d
   40f95:	rol    ecx,0xa
   40f98:	xor    ecx,edx
   40f9a:	mov    r10,rsi
   40f9d:	mov    ebx,r10d
   40fa0:	and    ebx,r14d
   40fa3:	mov    ebp,r10d
   40fa6:	xor    ebp,r14d
   40fa9:	and    ebp,r12d
   40fac:	xor    ebp,ebx
   40fae:	add    ebp,ecx
   40fb0:	add    ebp,eax
   40fb2:	add    r15d,eax
   40fb5:	mov    eax,r15d
   40fb8:	rol    eax,0x1a
   40fbb:	mov    ecx,r15d
   40fbe:	rol    ecx,0x15
   40fc1:	xor    ecx,eax
   40fc3:	mov    eax,r15d
   40fc6:	rol    eax,0x7
   40fc9:	xor    eax,ecx
   40fcb:	lea    ecx,[r9+r13*1]
   40fcf:	mov    r9d,r11d
   40fd2:	xor    r9d,edi
   40fd5:	and    r9d,r15d
   40fd8:	xor    r9d,edi
   40fdb:	add    r9d,ecx
   40fde:	mov    ecx,ebp
   40fe0:	rol    ecx,0x1e
   40fe3:	add    eax,r9d
   40fe6:	add    eax,0x6ca6351
   40feb:	mov    r9d,ebp
   40fee:	rol    r9d,0x13
   40ff2:	xor    r9d,ecx
   40ff5:	mov    ecx,ebp
   40ff7:	rol    ecx,0xa
   40ffa:	xor    ecx,r9d
   40ffd:	mov    r9d,r12d
   41000:	xor    r9d,r10d
   41003:	and    r9d,ebp
   41006:	mov    edx,r12d
   41009:	and    edx,r10d
   4100c:	xor    edx,r9d
   4100f:	add    edx,ecx
   41011:	mov    rsi,rdx
   41014:	add    r14d,eax
   41017:	mov    ecx,r14d
   4101a:	rol    ecx,0x1a
   4101d:	add    esi,eax
   4101f:	mov    eax,r14d
   41022:	rol    eax,0x15
   41025:	xor    eax,ecx
   41027:	mov    ecx,r14d
   4102a:	mov    QWORD PTR [rsp+0x20],r14
   4102f:	rol    ecx,0x7
   41032:	xor    ecx,eax
   41034:	mov    rax,QWORD PTR [rsp+0x8]
   41039:	add    eax,edi
   4103b:	mov    edi,r15d
   4103e:	mov    DWORD PTR [rsp+0x28],r11d
   41043:	xor    edi,r11d
   41046:	and    edi,r14d
   41049:	xor    edi,r11d
   4104c:	add    edi,eax
   4104e:	lea    edx,[rcx+rdi*1]
   41051:	add    edx,0x14292967
   41057:	mov    ecx,esi
   41059:	rol    ecx,0x1e
   4105c:	mov    r9d,esi
   4105f:	rol    r9d,0x13
   41063:	xor    r9d,ecx
   41066:	mov    edi,esi
   41068:	mov    rcx,rsi
   4106b:	mov    QWORD PTR [rsp+0x70],rsi
   41070:	rol    edi,0xa
   41073:	xor    edi,r9d
   41076:	mov    r9d,ebp
   41079:	and    r9d,r12d
   4107c:	mov    ebx,DWORD PTR [rsp+0x38]
   41080:	mov    eax,ebx
   41082:	rol    eax,0x19
   41085:	mov    r8,QWORD PTR [rsp+0x60]
   4108a:	mov    r14d,r8d
   4108d:	rol    r14d,0x19
   41091:	mov    r11d,ebp
   41094:	xor    r11d,r12d
   41097:	mov    rsi,QWORD PTR [rsp+0x48]
   4109c:	mov    r13d,esi
   4109f:	rol    r13d,0x19
   410a3:	mov    DWORD PTR [rsp+0x68],r13d
   410a8:	and    r11d,ecx
   410ab:	mov    rcx,QWORD PTR [rsp+0x88]
   410b3:	mov    r13d,ecx
   410b6:	rol    r13d,0x19
   410ba:	mov    DWORD PTR [rsp+0xa0],r13d
   410c2:	xor    r11d,r9d
   410c5:	mov    r9d,ebx
   410c8:	rol    r9d,0xe
   410cc:	add    r11d,edi
   410cf:	mov    edi,r8d
   410d2:	rol    edi,0xe
   410d5:	add    r11d,edx
   410d8:	mov    ebx,esi
   410da:	rol    ebx,0xe
   410dd:	add    r10d,edx
   410e0:	mov    QWORD PTR [rsp+0xc0],r10
   410e8:	mov    edx,ecx
   410ea:	rol    edx,0xe
   410ed:	mov    esi,edx
   410ef:	xor    r9d,eax
   410f2:	mov    DWORD PTR [rsp+0x80],r9d
   410fa:	mov    r13d,DWORD PTR [rsp+0x34]
   410ff:	mov    ecx,r13d
   41102:	rol    ecx,0x19
   41105:	mov    r10d,edi
   41108:	xor    r10d,r14d
   4110b:	mov    rdi,QWORD PTR [rsp+0x50]
   41110:	mov    edx,edi
   41112:	rol    edx,0x19
   41115:	xor    ebx,DWORD PTR [rsp+0x68]
   41119:	mov    r14,QWORD PTR [rsp+0x58]
   4111e:	mov    r9d,r14d
   41121:	rol    r9d,0x19
   41125:	xor    esi,DWORD PTR [rsp+0xa0]
   4112c:	mov    DWORD PTR [rsp+0x68],esi
   41130:	mov    eax,r13d
   41133:	rol    eax,0xe
   41136:	xor    eax,ecx
   41138:	mov    ecx,edi
   4113a:	rol    ecx,0xe
   4113d:	xor    ecx,edx
   4113f:	mov    edx,r14d
   41142:	rol    edx,0xe
   41145:	xor    edx,r9d
   41148:	mov    r8,QWORD PTR [rsp]
   4114c:	mov    r9d,r8d
   4114f:	rol    r9d,0x19
   41153:	mov    esi,r8d
   41156:	rol    esi,0xe
   41159:	xor    esi,r9d
   4115c:	shr    r13d,0x3
   41160:	xor    r13d,eax
   41163:	add    r13d,edi
   41166:	mov    DWORD PTR [rsp+0xa0],r13d
   4116e:	shr    edi,0x3
   41171:	xor    edi,ecx
   41173:	mov    rcx,r14
   41176:	add    edi,ecx
   41178:	mov    QWORD PTR [rsp+0x50],rdi
   4117d:	shr    ecx,0x3
   41180:	xor    ecx,edx
   41182:	mov    rax,r8
   41185:	add    ecx,eax
   41187:	mov    QWORD PTR [rsp+0x58],rcx
   4118c:	shr    eax,0x3
   4118f:	xor    eax,esi
   41191:	mov    r8d,DWORD PTR [rsp+0x38]
   41196:	add    eax,r8d
   41199:	mov    QWORD PTR [rsp],rax
   4119d:	shr    r8d,0x3
   411a1:	xor    r8d,DWORD PTR [rsp+0x80]
   411a9:	mov    r13,QWORD PTR [rsp+0x60]
   411ae:	add    r8d,r13d
   411b1:	shr    r13d,0x3
   411b5:	xor    r13d,r10d
   411b8:	mov    rcx,QWORD PTR [rsp+0x48]
   411bd:	add    r13d,ecx
   411c0:	shr    ecx,0x3
   411c3:	xor    ecx,ebx
   411c5:	mov    rdx,QWORD PTR [rsp+0x88]
   411cd:	add    ecx,edx
   411cf:	mov    rbx,rcx
   411d2:	shr    edx,0x3
   411d5:	xor    edx,DWORD PTR [rsp+0x68]
   411d9:	mov    rdi,QWORD PTR [rsp+0x10]
   411de:	mov    ecx,edi
   411e0:	rol    ecx,0xf
   411e3:	add    edx,DWORD PTR [rsp+0x78]
   411e7:	mov    rsi,rdx
   411ea:	mov    edx,edi
   411ec:	rol    edx,0xd
   411ef:	xor    edx,ecx
   411f1:	mov    r9d,edi
   411f4:	shr    r9d,0xa
   411f8:	xor    r9d,edx
   411fb:	add    esi,DWORD PTR [rsp+0x98]
   41202:	mov    rax,QWORD PTR [rsp+0x8]
   41207:	mov    ecx,eax
   41209:	rol    ecx,0xf
   4120c:	add    r9d,esi
   4120f:	mov    edx,eax
   41211:	rol    edx,0xd
   41214:	xor    edx,ecx
   41216:	mov    esi,eax
   41218:	shr    esi,0xa
   4121b:	xor    esi,edx
   4121d:	add    ebx,DWORD PTR [rsp+0x18]
   41221:	mov    ecx,r9d
   41224:	rol    ecx,0xf
   41227:	add    esi,ebx
   41229:	mov    edx,r9d
   4122c:	rol    edx,0xd
   4122f:	xor    edx,ecx
   41231:	mov    ebx,r9d
   41234:	shr    ebx,0xa
   41237:	xor    ebx,edx
   41239:	add    r13d,DWORD PTR [rsp+0xb0]
   41241:	mov    ecx,esi
   41243:	rol    ecx,0xf
   41246:	add    ebx,r13d
   41249:	mov    edx,esi
   4124b:	rol    edx,0xd
   4124e:	xor    edx,ecx
   41250:	mov    edi,esi
   41252:	mov    QWORD PTR [rsp+0x88],rsi
   4125a:	shr    edi,0xa
   4125d:	xor    edi,edx
   4125f:	add    r8d,DWORD PTR [rsp+0xa8]
   41267:	mov    r14,QWORD PTR [rsp+0xc0]
   4126f:	mov    ecx,r14d
   41272:	rol    ecx,0x1a
   41275:	add    edi,r8d
   41278:	mov    eax,r14d
   4127b:	rol    eax,0x15
   4127e:	xor    eax,ecx
   41280:	mov    ecx,r14d
   41283:	rol    ecx,0x7
   41286:	xor    ecx,eax
   41288:	mov    edx,DWORD PTR [rsp+0x28]
   4128c:	add    edx,r9d
   4128f:	mov    DWORD PTR [rsp+0x68],r9d
   41294:	mov    r13,QWORD PTR [rsp+0x20]
   41299:	mov    eax,r13d
   4129c:	xor    eax,r15d
   4129f:	and    eax,r14d
   412a2:	xor    eax,r15d
   412a5:	add    eax,edx
   412a7:	add    eax,ecx
   412a9:	add    eax,0x27b70a85
   412ae:	mov    ecx,r11d
   412b1:	rol    ecx,0x1e
   412b4:	mov    edx,r11d
   412b7:	rol    edx,0x13
   412ba:	xor    edx,ecx
   412bc:	mov    ecx,r11d
   412bf:	rol    ecx,0xa
   412c2:	xor    ecx,edx
   412c4:	mov    r10,QWORD PTR [rsp+0x70]
   412c9:	mov    edx,r10d
   412cc:	xor    edx,ebp
   412ce:	and    edx,r11d
   412d1:	mov    r8d,r10d
   412d4:	and    r8d,ebp
   412d7:	xor    r8d,edx
   412da:	add    r8d,ecx
   412dd:	add    r8d,eax
   412e0:	add    r12d,eax
   412e3:	mov    eax,r12d
   412e6:	rol    eax,0x1a
   412e9:	mov    ecx,r12d
   412ec:	rol    ecx,0x15
   412ef:	xor    ecx,eax
   412f1:	mov    eax,r12d
   412f4:	rol    eax,0x7
   412f7:	xor    eax,ecx
   412f9:	lea    ecx,[rsi+r15*1]
   412fd:	mov    edx,r14d
   41300:	mov    rsi,r13
   41303:	xor    edx,esi
   41305:	and    edx,r12d
   41308:	mov    r15d,r12d
   4130b:	xor    edx,esi
   4130d:	add    edx,ecx
   4130f:	mov    ecx,r8d
   41312:	rol    ecx,0x1e
   41315:	add    eax,edx
   41317:	add    eax,0x2e1b2138
   4131c:	mov    edx,r8d
   4131f:	rol    edx,0x13
   41322:	xor    edx,ecx
   41324:	mov    ecx,r8d
   41327:	rol    ecx,0xa
   4132a:	xor    ecx,edx
   4132c:	mov    edx,r11d
   4132f:	and    edx,r10d
   41332:	mov    r13d,r11d
   41335:	xor    r13d,r10d
   41338:	and    r13d,r8d
   4133b:	xor    r13d,edx
   4133e:	add    r13d,ecx
   41341:	add    ebp,eax
   41343:	mov    ecx,ebp
   41345:	rol    ecx,0x1a
   41348:	add    r13d,eax
   4134b:	mov    eax,ebp
   4134d:	rol    eax,0x15
   41350:	xor    eax,ecx
   41352:	mov    ecx,ebp
   41354:	rol    ecx,0x7
   41357:	xor    ecx,eax
   41359:	mov    edx,r12d
   4135c:	xor    edx,r14d
   4135f:	and    edx,ebp
   41361:	xor    edx,r14d
   41364:	add    edx,ebx
   41366:	add    edx,esi
   41368:	lea    eax,[rcx+rdx*1]
   4136b:	add    eax,0x4d2c6dfc
   41370:	mov    ecx,r13d
   41373:	rol    ecx,0x1e
   41376:	mov    edx,r13d
   41379:	rol    edx,0x13
   4137c:	xor    edx,ecx
   4137e:	mov    ecx,r13d
   41381:	rol    ecx,0xa
   41384:	xor    ecx,edx
   41386:	mov    edx,r8d
   41389:	xor    edx,r11d
   4138c:	and    edx,r13d
   4138f:	mov    r12d,r8d
   41392:	and    r12d,r11d
   41395:	xor    r12d,edx
   41398:	add    r12d,ecx
   4139b:	add    r12d,eax
   4139e:	mov    rsi,r10
   413a1:	add    esi,eax
   413a3:	mov    eax,esi
   413a5:	rol    eax,0x1a
   413a8:	mov    ecx,esi
   413aa:	rol    ecx,0x15
   413ad:	xor    ecx,eax
   413af:	mov    eax,esi
   413b1:	rol    eax,0x7
   413b4:	xor    eax,ecx
   413b6:	lea    ecx,[rdi+r14*1]
   413ba:	mov    edx,ebp
   413bc:	xor    edx,r15d
   413bf:	and    edx,esi
   413c1:	mov    r10,rsi
   413c4:	xor    edx,r15d
   413c7:	add    edx,ecx
   413c9:	mov    ecx,r12d
   413cc:	rol    ecx,0x1e
   413cf:	add    eax,edx
   413d1:	add    eax,0x53380d13
   413d6:	mov    edx,r12d
   413d9:	rol    edx,0x13
   413dc:	xor    edx,ecx
   413de:	mov    ecx,r12d
   413e1:	rol    ecx,0xa
   413e4:	xor    ecx,edx
   413e6:	mov    edx,r13d
   413e9:	and    edx,r8d
   413ec:	mov    esi,r13d
   413ef:	xor    esi,r8d
   413f2:	and    esi,r12d
   413f5:	xor    esi,edx
   413f7:	add    esi,ecx
   413f9:	add    esi,eax
   413fb:	mov    r14,rsi
   413fe:	mov    QWORD PTR [rsp+0x80],rbx
   41406:	mov    ecx,ebx
   41408:	rol    ecx,0xf
   4140b:	add    r11d,eax
   4140e:	mov    eax,ebx
   41410:	rol    eax,0xd
   41413:	xor    eax,ecx
   41415:	mov    edx,ebx
   41417:	shr    edx,0xa
   4141a:	xor    edx,eax
   4141c:	mov    rcx,QWORD PTR [rsp]
   41420:	add    ecx,DWORD PTR [rsp+0x40]
   41424:	mov    QWORD PTR [rsp+0x38],rdi
   41429:	mov    eax,edi
   4142b:	rol    eax,0xf
   4142e:	add    edx,ecx
   41430:	mov    ecx,edi
   41432:	rol    ecx,0xd
   41435:	xor    ecx,eax
   41437:	mov    esi,edi
   41439:	shr    esi,0xa
   4143c:	xor    esi,ecx
   4143e:	mov    rcx,QWORD PTR [rsp+0x58]
   41443:	add    ecx,DWORD PTR [rsp+0x10]
   41447:	mov    eax,edx
   41449:	rol    eax,0xf
   4144c:	add    esi,ecx
   4144e:	mov    ecx,edx
   41450:	rol    ecx,0xd
   41453:	xor    ecx,eax
   41455:	mov    edi,edx
   41457:	mov    DWORD PTR [rsp+0x78],edx
   4145b:	shr    edi,0xa
   4145e:	xor    edi,ecx
   41460:	mov    rcx,QWORD PTR [rsp+0x50]
   41465:	add    ecx,DWORD PTR [rsp+0x8]
   41469:	mov    eax,esi
   4146b:	rol    eax,0xf
   4146e:	add    edi,ecx
   41470:	mov    QWORD PTR [rsp],rdi
   41474:	mov    ecx,esi
   41476:	rol    ecx,0xd
   41479:	xor    ecx,eax
   4147b:	mov    eax,esi
   4147d:	mov    rbx,rsi
   41480:	mov    QWORD PTR [rsp+0x48],rsi
   41485:	shr    eax,0xa
   41488:	xor    eax,ecx
   4148a:	mov    rcx,rax
   4148d:	mov    esi,DWORD PTR [rsp+0xa0]
   41494:	add    esi,r9d
   41497:	mov    eax,r11d
   4149a:	rol    eax,0x1a
   4149d:	add    ecx,esi
   4149f:	mov    QWORD PTR [rsp+0x20],rcx
   414a4:	mov    ecx,r11d
   414a7:	rol    ecx,0x15
   414aa:	xor    ecx,eax
   414ac:	mov    eax,r11d
   414af:	rol    eax,0x7
   414b2:	xor    eax,ecx
   414b4:	add    r15d,edx
   414b7:	mov    ecx,r10d
   414ba:	xor    ecx,ebp
   414bc:	and    ecx,r11d
   414bf:	xor    ecx,ebp
   414c1:	add    ecx,r15d
   414c4:	add    ecx,eax
   414c6:	add    ecx,0x650a7354
   414cc:	mov    r15,r14
   414cf:	mov    eax,r15d
   414d2:	rol    eax,0x1e
   414d5:	mov    edx,r15d
   414d8:	rol    edx,0x13
   414db:	xor    edx,eax
   414dd:	mov    r9d,r15d
   414e0:	rol    r9d,0xa
   414e4:	xor    r9d,edx
   414e7:	mov    edx,r12d
   414ea:	xor    edx,r13d
   414ed:	and    edx,r15d
   414f0:	mov    eax,r12d
   414f3:	and    eax,r13d
   414f6:	xor    eax,edx
   414f8:	add    eax,r9d
   414fb:	add    eax,ecx
   414fd:	mov    esi,r8d
   41500:	add    esi,ecx
   41502:	mov    ecx,esi
   41504:	rol    ecx,0x1a
   41507:	mov    edx,esi
   41509:	rol    edx,0x15
   4150c:	xor    edx,ecx
   4150e:	mov    ecx,esi
   41510:	rol    ecx,0x7
   41513:	xor    ecx,edx
   41515:	lea    edx,[rbx+rbp*1]
   41518:	mov    r9d,r11d
   4151b:	xor    r9d,r10d
   4151e:	and    r9d,esi
   41521:	xor    r9d,r10d
   41524:	mov    r8,r10
   41527:	add    r9d,edx
   4152a:	mov    edx,eax
   4152c:	rol    edx,0x1e
   4152f:	add    ecx,r9d
   41532:	add    ecx,0x766a0abb
   41538:	mov    r9d,eax
   4153b:	rol    r9d,0x13
   4153f:	xor    r9d,edx
   41542:	mov    edx,eax
   41544:	mov    ebp,eax
   41546:	rol    edx,0xa
   41549:	xor    edx,r9d
   4154c:	mov    r10d,r15d
   4154f:	and    r10d,r12d
   41552:	mov    eax,r15d
   41555:	xor    eax,r12d
   41558:	and    eax,ebp
   4155a:	xor    eax,r10d
   4155d:	add    eax,edx
   4155f:	mov    rbx,rax
   41562:	add    r13d,ecx
   41565:	mov    edx,r13d
   41568:	rol    edx,0x1a
   4156b:	add    ebx,ecx
   4156d:	mov    ecx,r13d
   41570:	rol    ecx,0x15
   41573:	xor    ecx,edx
   41575:	mov    edx,r13d
   41578:	rol    edx,0x7
   4157b:	xor    edx,ecx
   4157d:	mov    r10d,esi
   41580:	xor    r10d,r11d
   41583:	and    r10d,r13d
   41586:	xor    r10d,r11d
   41589:	add    r10d,edi
   4158c:	add    r10d,r8d
   4158f:	lea    ecx,[rdx+r10*1]
   41593:	add    ecx,0x81c2c92e
   41599:	mov    edx,ebx
   4159b:	rol    edx,0x1e
   4159e:	mov    r10d,ebx
   415a1:	rol    r10d,0x13
   415a5:	xor    r10d,edx
   415a8:	mov    edx,ebx
   415aa:	rol    edx,0xa
   415ad:	xor    edx,r10d
   415b0:	mov    r10d,ebp
   415b3:	mov    QWORD PTR [rsp+0x70],r14
   415b8:	xor    r10d,r15d
   415bb:	and    r10d,ebx
   415be:	mov    eax,ebp
   415c0:	and    eax,r15d
   415c3:	xor    eax,r10d
   415c6:	add    eax,edx
   415c8:	add    eax,ecx
   415ca:	mov    rdi,rax
   415cd:	add    r12d,ecx
   415d0:	mov    ecx,r12d
   415d3:	rol    ecx,0x1a
   415d6:	mov    edx,r12d
   415d9:	rol    edx,0x15
   415dc:	xor    edx,ecx
   415de:	mov    ecx,r12d
   415e1:	mov    QWORD PTR [rsp+0x50],r12
   415e6:	rol    ecx,0x7
   415e9:	xor    ecx,edx
   415eb:	mov    rax,QWORD PTR [rsp+0x20]
   415f0:	lea    edx,[rax+r11*1]
   415f4:	mov    r8d,r13d
   415f7:	mov    DWORD PTR [rsp+0xc0],esi
   415fe:	xor    r8d,esi
   41601:	and    r8d,r12d
   41604:	xor    r8d,esi
   41607:	add    r8d,edx
   4160a:	mov    edx,edi
   4160c:	rol    edx,0x1e
   4160f:	lea    r9d,[rcx+r8*1]
   41613:	add    r9d,0x92722c85
   4161a:	mov    ecx,edi
   4161c:	rol    ecx,0x13
   4161f:	xor    ecx,edx
   41621:	mov    r14d,edi
   41624:	mov    QWORD PTR [rsp+0xc8],rdi
   4162c:	rol    r14d,0xa
   41630:	xor    r14d,ecx
   41633:	mov    esi,DWORD PTR [rsp+0xa8]
   4163a:	mov    r10d,esi
   4163d:	rol    r10d,0x19
   41641:	mov    rdx,QWORD PTR [rsp+0xb0]
   41649:	mov    eax,edx
   4164b:	rol    eax,0x19
   4164e:	mov    DWORD PTR [rsp+0x28],eax
   41652:	mov    r15,rbx
   41655:	mov    QWORD PTR [rsp+0xb8],rbx
   4165d:	mov    r11d,r15d
   41660:	mov    DWORD PTR [rsp+0xa0],ebp
   41667:	and    r11d,ebp
   4166a:	mov    rcx,QWORD PTR [rsp+0x18]
   4166f:	mov    r12d,ecx
   41672:	rol    r12d,0x19
   41676:	mov    rax,QWORD PTR [rsp+0x98]
   4167e:	mov    r8d,eax
   41681:	rol    r8d,0x19
   41685:	mov    DWORD PTR [rsp+0x60],r8d
   4168a:	xor    r15d,ebp
   4168d:	mov    r8d,esi
   41690:	rol    r8d,0xe
   41694:	mov    ebx,r8d
   41697:	and    r15d,edi
   4169a:	mov    esi,edx
   4169c:	rol    esi,0xe
   4169f:	xor    r15d,r11d
   416a2:	mov    r8d,ecx
   416a5:	rol    r8d,0xe
   416a9:	add    r15d,r14d
   416ac:	rol    eax,0xe
   416af:	mov    DWORD PTR [rsp+0x58],eax
   416b3:	add    r15d,r9d
   416b6:	mov    QWORD PTR [rsp+0xf0],r15
   416be:	mov    eax,DWORD PTR [rsp+0x68]
   416c2:	mov    ecx,eax
   416c4:	rol    ecx,0x19
   416c7:	mov    rdi,QWORD PTR [rsp+0x70]
   416cc:	add    edi,r9d
   416cf:	mov    QWORD PTR [rsp+0x70],rdi
   416d4:	mov    r9,QWORD PTR [rsp+0x8]
   416d9:	mov    edx,r9d
   416dc:	rol    edx,0x19
   416df:	mov    r11d,ebx
   416e2:	xor    r11d,r10d
   416e5:	mov    rbp,QWORD PTR [rsp+0x10]
   416ea:	mov    r10d,ebp
   416ed:	rol    r10d,0x19
   416f1:	mov    ebx,esi
   416f3:	xor    ebx,DWORD PTR [rsp+0x28]
   416f7:	mov    rdi,QWORD PTR [rsp+0x40]
   416fc:	mov    esi,edi
   416fe:	rol    esi,0x19
   41701:	mov    r14d,r8d
   41704:	xor    r14d,r12d
   41707:	mov    r12d,eax
   4170a:	mov    r8d,eax
   4170d:	rol    r12d,0xe
   41711:	mov    r15d,DWORD PTR [rsp+0x58]
   41716:	xor    r15d,DWORD PTR [rsp+0x60]
   4171b:	mov    eax,r9d
   4171e:	rol    eax,0xe
   41721:	xor    r12d,ecx
   41724:	mov    ecx,ebp
   41726:	rol    ecx,0xe
   41729:	xor    eax,edx
   4172b:	mov    edx,edi
   4172d:	rol    edx,0xe
   41730:	xor    ecx,r10d
   41733:	xor    edx,esi
   41735:	mov    esi,r8d
   41738:	shr    esi,0x3
   4173b:	xor    esi,r12d
   4173e:	add    esi,r9d
   41741:	shr    r9d,0x3
   41745:	xor    r9d,eax
   41748:	mov    rax,rbp
   4174b:	add    r9d,eax
   4174e:	mov    QWORD PTR [rsp+0x8],r9
   41753:	shr    eax,0x3
   41756:	xor    eax,ecx
   41758:	add    eax,edi
   4175a:	mov    QWORD PTR [rsp+0x10],rax
   4175f:	shr    edi,0x3
   41762:	xor    edi,edx
   41764:	mov    r10d,DWORD PTR [rsp+0xa8]
   4176c:	add    edi,r10d
   4176f:	mov    QWORD PTR [rsp+0x40],rdi
   41774:	shr    r10d,0x3
   41778:	xor    r10d,r11d
   4177b:	mov    r12,QWORD PTR [rsp+0xb0]
   41783:	add    r10d,r12d
   41786:	shr    r12d,0x3
   4178a:	xor    r12d,ebx
   4178d:	mov    rax,QWORD PTR [rsp+0x18]
   41792:	add    r12d,eax
   41795:	shr    eax,0x3
   41798:	xor    eax,r14d
   4179b:	mov    rcx,QWORD PTR [rsp+0x98]
   417a3:	add    eax,ecx
   417a5:	mov    r11,rax
   417a8:	shr    ecx,0x3
   417ab:	xor    ecx,r15d
   417ae:	add    ecx,DWORD PTR [rsp+0x34]
   417b2:	mov    r8,rcx
   417b5:	mov    rdx,QWORD PTR [rsp]
   417b9:	mov    eax,edx
   417bb:	rol    eax,0xf
   417be:	mov    ecx,edx
   417c0:	rol    ecx,0xd
   417c3:	xor    ecx,eax
   417c5:	shr    edx,0xa
   417c8:	xor    edx,ecx
   417ca:	add    r8d,DWORD PTR [rsp+0x88]
   417d2:	add    edx,r8d
   417d5:	mov    r8,QWORD PTR [rsp+0x20]
   417da:	mov    eax,r8d
   417dd:	rol    eax,0xf
   417e0:	mov    ecx,r8d
   417e3:	rol    ecx,0xd
   417e6:	xor    ecx,eax
   417e8:	shr    r8d,0xa
   417ec:	xor    r8d,ecx
   417ef:	add    r11d,DWORD PTR [rsp+0x80]
   417f7:	add    r8d,r11d
   417fa:	mov    eax,edx
   417fc:	rol    eax,0xf
   417ff:	mov    ecx,edx
   41801:	rol    ecx,0xd
   41804:	xor    ecx,eax
   41806:	mov    eax,edx
   41808:	mov    DWORD PTR [rsp+0x58],edx
   4180c:	shr    eax,0xa
   4180f:	xor    eax,ecx
   41811:	add    r12d,DWORD PTR [rsp+0x38]
   41816:	add    eax,r12d
   41819:	mov    r14,rax
   4181c:	mov    eax,r8d
   4181f:	rol    eax,0xf
   41822:	mov    ecx,r8d
   41825:	rol    ecx,0xd
   41828:	xor    ecx,eax
   4182a:	mov    eax,r8d
   4182d:	mov    r11,r8
   41830:	mov    QWORD PTR [rsp+0x60],r8
   41835:	shr    eax,0xa
   41838:	xor    eax,ecx
   4183a:	add    r10d,DWORD PTR [rsp+0x78]
   4183f:	add    eax,r10d
   41842:	mov    r8,rax
   41845:	mov    rbp,QWORD PTR [rsp+0x70]
   4184a:	mov    eax,ebp
   4184c:	rol    eax,0x1a
   4184f:	mov    ecx,ebp
   41851:	rol    ecx,0x15
   41854:	xor    ecx,eax
   41856:	mov    eax,ebp
   41858:	rol    eax,0x7
   4185b:	xor    eax,ecx
   4185d:	mov    edi,DWORD PTR [rsp+0xc0]
   41864:	add    edi,edx
   41866:	mov    r10,QWORD PTR [rsp+0x50]
   4186b:	mov    ecx,r10d
   4186e:	xor    ecx,r13d
   41871:	and    ecx,ebp
   41873:	xor    ecx,r13d
   41876:	add    ecx,edi
   41878:	mov    r15,QWORD PTR [rsp+0xf0]
   41880:	mov    edx,r15d
   41883:	rol    edx,0x1e
   41886:	add    eax,ecx
   41888:	add    eax,0xa2bfe8a1
   4188d:	mov    ecx,r15d
   41890:	rol    ecx,0x13
   41893:	xor    ecx,edx
   41895:	mov    edx,r15d
   41898:	rol    edx,0xa
   4189b:	xor    edx,ecx
   4189d:	mov    r12,QWORD PTR [rsp+0xc8]
   418a5:	mov    ecx,r12d
   418a8:	mov    rbx,QWORD PTR [rsp+0xb8]
   418b0:	xor    ecx,ebx
   418b2:	and    ecx,r15d
   418b5:	mov    edi,r12d
   418b8:	and    edi,ebx
   418ba:	xor    edi,ecx
   418bc:	add    edi,edx
   418be:	mov    r9d,DWORD PTR [rsp+0xa0]
   418c6:	add    r9d,eax
   418c9:	mov    ecx,r9d
   418cc:	rol    ecx,0x1a
   418cf:	add    edi,eax
   418d1:	mov    eax,r9d
   418d4:	rol    eax,0x15
   418d7:	xor    eax,ecx
   418d9:	mov    ecx,r9d
   418dc:	rol    ecx,0x7
   418df:	xor    ecx,eax
   418e1:	mov    edx,ebp
   418e3:	xor    edx,r10d
   418e6:	and    edx,r9d
   418e9:	xor    edx,r10d
   418ec:	add    edx,r11d
   418ef:	add    edx,r13d
   418f2:	lea    eax,[rcx+rdx*1]
   418f5:	add    eax,0xa81a664b
   418fa:	mov    ecx,edi
   418fc:	rol    ecx,0x1e
   418ff:	mov    edx,edi
   41901:	rol    edx,0x13
   41904:	xor    edx,ecx
   41906:	mov    ecx,edi
   41908:	rol    ecx,0xa
   4190b:	xor    ecx,edx
   4190d:	mov    edx,r15d
   41910:	and    edx,r12d
   41913:	mov    r11d,r15d
   41916:	xor    r11d,r12d
   41919:	and    r11d,edi
   4191c:	xor    r11d,edx
   4191f:	add    r11d,ecx
   41922:	add    r11d,eax
   41925:	add    ebx,eax
   41927:	mov    eax,ebx
   41929:	rol    eax,0x1a
   4192c:	mov    ecx,ebx
   4192e:	rol    ecx,0x15
   41931:	xor    ecx,eax
   41933:	mov    eax,ebx
   41935:	rol    eax,0x7
   41938:	xor    eax,ecx
   4193a:	mov    edx,r9d
   4193d:	xor    edx,ebp
   4193f:	and    edx,ebx
   41941:	xor    edx,ebp
   41943:	add    edx,r14d
   41946:	add    edx,r10d
   41949:	mov    ecx,r11d
   4194c:	rol    ecx,0x1e
   4194f:	add    eax,edx
   41951:	add    eax,0xc24b8b70
   41956:	mov    edx,r11d
   41959:	rol    edx,0x13
   4195c:	xor    edx,ecx
   4195e:	mov    ecx,r11d
   41961:	rol    ecx,0xa
   41964:	xor    ecx,edx
   41966:	mov    edx,edi
   41968:	xor    edx,r15d
   4196b:	and    edx,r11d
   4196e:	mov    r10d,edi
   41971:	and    r10d,r15d
   41974:	xor    r10d,edx
   41977:	add    r10d,ecx
   4197a:	mov    r13,r12
   4197d:	add    r13d,eax
   41980:	mov    ecx,r13d
   41983:	rol    ecx,0x1a
   41986:	add    r10d,eax
   41989:	mov    r12,r10
   4198c:	mov    eax,r13d
   4198f:	rol    eax,0x15
   41992:	xor    eax,ecx
   41994:	mov    ecx,r13d
   41997:	rol    ecx,0x7
   4199a:	xor    ecx,eax
   4199c:	mov    edx,ebx
   4199e:	xor    edx,r9d
   419a1:	and    edx,r13d
   419a4:	xor    edx,r9d
   419a7:	add    edx,r8d
   419aa:	add    edx,ebp
   419ac:	lea    eax,[rcx+rdx*1]
   419af:	add    eax,0xc76c51a3
   419b4:	mov    ecx,r12d
   419b7:	rol    ecx,0x1e
   419ba:	mov    edx,r12d
   419bd:	rol    edx,0x13
   419c0:	xor    edx,ecx
   419c2:	mov    ecx,r12d
   419c5:	rol    ecx,0xa
   419c8:	xor    ecx,edx
   419ca:	mov    edx,r11d
   419cd:	and    edx,edi
   419cf:	mov    r10d,r11d
   419d2:	xor    r10d,edi
   419d5:	and    r10d,r12d
   419d8:	xor    r10d,edx
   419db:	add    r10d,ecx
   419de:	add    r10d,eax
   419e1:	add    r15d,eax
   419e4:	mov    QWORD PTR [rsp+0x28],r14
   419e9:	mov    eax,r14d
   419ec:	rol    eax,0xf
   419ef:	mov    ecx,r14d
   419f2:	rol    ecx,0xd
   419f5:	xor    ecx,eax
   419f7:	mov    edx,r14d
   419fa:	shr    edx,0xa
   419fd:	xor    edx,ecx
   419ff:	mov    rax,QWORD PTR [rsp+0x40]
   41a04:	add    eax,DWORD PTR [rsp+0x48]
   41a08:	add    edx,eax
   41a0a:	mov    QWORD PTR [rsp+0x18],r8
   41a0f:	mov    eax,r8d
   41a12:	rol    eax,0xf
   41a15:	mov    ecx,r8d
   41a18:	rol    ecx,0xd
   41a1b:	xor    ecx,eax
   41a1d:	mov    r14d,r8d
   41a20:	shr    r14d,0xa
   41a24:	xor    r14d,ecx
   41a27:	mov    rax,QWORD PTR [rsp+0x10]
   41a2c:	add    eax,DWORD PTR [rsp]
   41a2f:	add    r14d,eax
   41a32:	mov    eax,edx
   41a34:	rol    eax,0xf
   41a37:	mov    ecx,edx
   41a39:	rol    ecx,0xd
   41a3c:	xor    ecx,eax
   41a3e:	mov    eax,edx
   41a40:	mov    DWORD PTR [rsp+0xb0],edx
   41a47:	shr    eax,0xa
   41a4a:	xor    eax,ecx
   41a4c:	mov    rcx,QWORD PTR [rsp+0x8]
   41a51:	add    ecx,DWORD PTR [rsp+0x20]
   41a55:	add    eax,ecx
   41a57:	mov    rbp,rax
   41a5a:	mov    QWORD PTR [rsp+0xa8],rax
   41a62:	mov    eax,r14d
   41a65:	rol    eax,0xf
   41a68:	mov    ecx,r14d
   41a6b:	rol    ecx,0xd
   41a6e:	xor    ecx,eax
   41a70:	mov    eax,r14d
   41a73:	mov    QWORD PTR [rsp+0x10],r14
   41a78:	shr    eax,0xa
   41a7b:	xor    eax,ecx
   41a7d:	add    esi,DWORD PTR [rsp+0x58]
   41a81:	add    eax,esi
   41a83:	mov    QWORD PTR [rsp+0x40],rax
   41a88:	mov    eax,r15d
   41a8b:	rol    eax,0x1a
   41a8e:	mov    ecx,r15d
   41a91:	rol    ecx,0x15
   41a94:	xor    ecx,eax
   41a96:	mov    eax,r15d
   41a99:	rol    eax,0x7
   41a9c:	xor    eax,ecx
   41a9e:	add    r9d,edx
   41aa1:	mov    ecx,r13d
   41aa4:	xor    ecx,ebx
   41aa6:	and    ecx,r15d
   41aa9:	xor    ecx,ebx
   41aab:	add    ecx,r9d
   41aae:	mov    edx,r10d
   41ab1:	rol    edx,0x1e
   41ab4:	add    eax,ecx
   41ab6:	add    eax,0xd192e819
   41abb:	mov    ecx,r10d
   41abe:	rol    ecx,0x13
   41ac1:	xor    ecx,edx
   41ac3:	mov    edx,r10d
   41ac6:	rol    edx,0xa
   41ac9:	xor    edx,ecx
   41acb:	mov    ecx,r12d
   41ace:	xor    ecx,r11d
   41ad1:	and    ecx,r10d
   41ad4:	mov    esi,r12d
   41ad7:	and    esi,r11d
   41ada:	xor    esi,ecx
   41adc:	add    esi,edx
   41ade:	add    edi,eax
   41ae0:	mov    ecx,edi
   41ae2:	rol    ecx,0x1a
   41ae5:	add    esi,eax
   41ae7:	mov    eax,edi
   41ae9:	rol    eax,0x15
   41aec:	xor    eax,ecx
   41aee:	mov    ecx,edi
   41af0:	mov    r9d,edi
   41af3:	rol    ecx,0x7
   41af6:	xor    ecx,eax
   41af8:	mov    edx,r15d
   41afb:	xor    edx,r13d
   41afe:	and    edx,edi
   41b00:	xor    edx,r13d
   41b03:	add    edx,r14d
   41b06:	add    edx,ebx
   41b08:	lea    eax,[rcx+rdx*1]
   41b0b:	add    eax,0xd6990624
   41b10:	mov    ecx,esi
   41b12:	rol    ecx,0x1e
   41b15:	mov    edx,esi
   41b17:	rol    edx,0x13
   41b1a:	xor    edx,ecx
   41b1c:	mov    ecx,esi
   41b1e:	rol    ecx,0xa
   41b21:	xor    ecx,edx
   41b23:	mov    edx,r10d
   41b26:	and    edx,r12d
   41b29:	mov    r8d,r10d
   41b2c:	xor    r8d,r12d
   41b2f:	and    r8d,esi
   41b32:	mov    edi,esi
   41b34:	xor    r8d,edx
   41b37:	add    r8d,ecx
   41b3a:	add    r8d,eax
   41b3d:	add    r11d,eax
   41b40:	mov    eax,r11d
   41b43:	rol    eax,0x1a
   41b46:	mov    ecx,r11d
   41b49:	rol    ecx,0x15
   41b4c:	xor    ecx,eax
   41b4e:	mov    eax,r11d
   41b51:	rol    eax,0x7
   41b54:	xor    eax,ecx
   41b56:	mov    edx,r9d
   41b59:	xor    edx,r15d
   41b5c:	and    edx,r11d
   41b5f:	xor    edx,r15d
   41b62:	add    edx,ebp
   41b64:	add    edx,r13d
   41b67:	mov    ecx,r8d
   41b6a:	rol    ecx,0x1e
   41b6d:	add    eax,edx
   41b6f:	add    eax,0xf40e3585
   41b74:	mov    edx,r8d
   41b77:	rol    edx,0x13
   41b7a:	xor    edx,ecx
   41b7c:	mov    ecx,r8d
   41b7f:	rol    ecx,0xa
   41b82:	xor    ecx,edx
   41b84:	mov    edx,esi
   41b86:	xor    edx,r10d
   41b89:	and    edx,r8d
   41b8c:	and    esi,r10d
   41b8f:	xor    esi,edx
   41b91:	add    esi,ecx
   41b93:	add    r12d,eax
   41b96:	mov    ecx,r12d
   41b99:	rol    ecx,0x1a
   41b9c:	add    esi,eax
   41b9e:	mov    eax,r12d
   41ba1:	rol    eax,0x15
   41ba4:	xor    eax,ecx
   41ba6:	mov    ecx,r12d
   41ba9:	mov    QWORD PTR [rsp+0x70],r12
   41bae:	rol    ecx,0x7
   41bb1:	xor    ecx,eax
   41bb3:	mov    rax,QWORD PTR [rsp+0x40]
   41bb8:	add    eax,r15d
   41bbb:	mov    edx,r11d
   41bbe:	mov    DWORD PTR [rsp+0x8],r9d
   41bc3:	xor    edx,r9d
   41bc6:	and    edx,r12d
   41bc9:	xor    edx,r9d
   41bcc:	add    edx,eax
   41bce:	lea    ebx,[rcx+rdx*1]
   41bd1:	add    ebx,0x106aa070
   41bd7:	mov    eax,esi
   41bd9:	rol    eax,0x1e
   41bdc:	mov    ecx,esi
   41bde:	rol    ecx,0x13
   41be1:	xor    ecx,eax
   41be3:	mov    edx,esi
   41be5:	mov    QWORD PTR [rsp+0xc0],rsi
   41bed:	rol    edx,0xa
   41bf0:	xor    edx,ecx
   41bf2:	mov    r15,r8
   41bf5:	mov    QWORD PTR [rsp+0xc8],r8
   41bfd:	mov    eax,r15d
   41c00:	mov    DWORD PTR [rsp+0x34],edi
   41c04:	and    eax,edi
   41c06:	mov    r8d,DWORD PTR [rsp+0x78]
   41c0b:	mov    r9d,r8d
   41c0e:	rol    r9d,0x19
   41c12:	mov    r12,QWORD PTR [rsp+0x38]
   41c17:	mov    r13d,r12d
   41c1a:	rol    r13d,0x19
   41c1e:	xor    r15d,edi
   41c21:	mov    rdi,QWORD PTR [rsp+0x80]
   41c29:	mov    r14d,edi
   41c2c:	rol    r14d,0x19
   41c30:	and    r15d,esi
   41c33:	mov    rsi,QWORD PTR [rsp+0x88]
   41c3b:	mov    ecx,esi
   41c3d:	rol    ecx,0x19
   41c40:	xor    r15d,eax
   41c43:	mov    eax,r8d
   41c46:	rol    eax,0xe
   41c49:	add    r15d,edx
   41c4c:	rol    r12d,0xe
   41c50:	add    r15d,ebx
   41c53:	mov    QWORD PTR [rsp+0xa0],r15
   41c5b:	mov    ebp,edi
   41c5d:	rol    ebp,0xe
   41c60:	add    r10d,ebx
   41c63:	mov    ebx,esi
   41c65:	rol    ebx,0xe
   41c68:	xor    eax,r9d
   41c6b:	mov    edi,eax
   41c6d:	mov    esi,DWORD PTR [rsp+0x58]
   41c71:	mov    r9d,esi
   41c74:	rol    r9d,0x19
   41c78:	xor    r12d,r13d
   41c7b:	mov    rdx,QWORD PTR [rsp+0x20]
   41c80:	mov    r15d,edx
   41c83:	rol    r15d,0x19
   41c87:	xor    ebp,r14d
   41c8a:	mov    r8,QWORD PTR [rsp]
   41c8e:	mov    r14d,r8d
   41c91:	rol    r14d,0x19
   41c95:	xor    ebx,ecx
   41c97:	mov    ecx,esi
   41c99:	rol    ecx,0xe
   41c9c:	xor    ecx,r9d
   41c9f:	mov    r9d,edx
   41ca2:	rol    r9d,0xe
   41ca6:	xor    r9d,r15d
   41ca9:	mov    r15d,r8d
   41cac:	rol    r15d,0xe
   41cb0:	xor    r15d,r14d
   41cb3:	mov    rax,QWORD PTR [rsp+0x48]
   41cb8:	mov    r14d,eax
   41cbb:	rol    r14d,0x19
   41cbf:	mov    r13d,eax
   41cc2:	rol    r13d,0xe
   41cc6:	xor    r13d,r14d
   41cc9:	mov    r14d,esi
   41ccc:	shr    r14d,0x3
   41cd0:	xor    r14d,ecx
   41cd3:	add    r14d,edx
   41cd6:	mov    DWORD PTR [rsp+0x98],r14d
   41cde:	shr    edx,0x3
   41ce1:	xor    edx,r9d
   41ce4:	mov    rcx,r8
   41ce7:	add    edx,ecx
   41ce9:	mov    QWORD PTR [rsp+0x20],rdx
   41cee:	shr    ecx,0x3
   41cf1:	xor    ecx,r15d
   41cf4:	add    ecx,eax
   41cf6:	mov    QWORD PTR [rsp],rcx
   41cfa:	shr    eax,0x3
   41cfd:	xor    eax,r13d
   41d00:	mov    ecx,DWORD PTR [rsp+0x78]
   41d04:	add    eax,ecx
   41d06:	mov    QWORD PTR [rsp+0x48],rax
   41d0b:	shr    ecx,0x3
   41d0e:	xor    ecx,edi
   41d10:	mov    r9,QWORD PTR [rsp+0x38]
   41d15:	add    ecx,r9d
   41d18:	shr    r9d,0x3
   41d1c:	xor    r9d,r12d
   41d1f:	mov    rax,QWORD PTR [rsp+0x80]
   41d27:	add    r9d,eax
   41d2a:	shr    eax,0x3
   41d2d:	xor    eax,ebp
   41d2f:	mov    rdx,QWORD PTR [rsp+0x88]
   41d37:	add    eax,edx
   41d39:	mov    r14,rax
   41d3c:	shr    edx,0x3
   41d3f:	xor    edx,ebx
   41d41:	mov    rdi,QWORD PTR [rsp+0xa8]
   41d49:	mov    eax,edi
   41d4b:	rol    eax,0xf
   41d4e:	add    edx,DWORD PTR [rsp+0x68]
   41d52:	mov    rbx,rdx
   41d55:	mov    edx,edi
   41d57:	rol    edx,0xd
   41d5a:	xor    edx,eax
   41d5c:	shr    edi,0xa
   41d5f:	xor    edi,edx
   41d61:	mov    r12,QWORD PTR [rsp+0x60]
   41d66:	add    ebx,r12d
   41d69:	mov    r15,QWORD PTR [rsp+0x40]
   41d6e:	mov    eax,r15d
   41d71:	rol    eax,0xf
   41d74:	add    edi,ebx
   41d76:	mov    edx,r15d
   41d79:	rol    edx,0xd
   41d7c:	xor    edx,eax
   41d7e:	shr    r15d,0xa
   41d82:	xor    r15d,edx
   41d85:	mov    rbp,QWORD PTR [rsp+0x28]
   41d8a:	add    r14d,ebp
   41d8d:	mov    eax,edi
   41d8f:	rol    eax,0xf
   41d92:	add    r15d,r14d
   41d95:	mov    edx,edi
   41d97:	rol    edx,0xd
   41d9a:	xor    edx,eax
   41d9c:	mov    ebx,r15d
   41d9f:	rol    ebx,0xf
   41da2:	mov    eax,r15d
   41da5:	rol    eax,0xd
   41da8:	mov    esi,edi
   41daa:	shr    esi,0xa
   41dad:	mov    r14d,r10d
   41db0:	rol    r14d,0x1a
   41db4:	xor    esi,edx
   41db6:	mov    edx,r10d
   41db9:	rol    edx,0x15
   41dbc:	mov    r8,QWORD PTR [rsp+0x18]
   41dc1:	add    r9d,r8d
   41dc4:	mov    r13d,r10d
   41dc7:	rol    r13d,0x7
   41dcb:	mov    QWORD PTR [rsp+0x50],r13
   41dd0:	add    esi,r9d
   41dd3:	mov    QWORD PTR [rsp+0x88],rsi
   41ddb:	mov    r13d,DWORD PTR [rsp+0xb0]
   41de3:	mov    esi,r13d
   41de6:	rol    esi,0x19
   41de9:	mov    DWORD PTR [rsp+0x68],esi
   41ded:	xor    eax,ebx
   41def:	mov    rbx,r8
   41df2:	mov    esi,ebx
   41df4:	rol    esi,0x19
   41df7:	mov    DWORD PTR [rsp+0x78],esi
   41dfb:	mov    rsi,rbp
   41dfe:	mov    r8d,ebp
   41e01:	rol    r8d,0x19
   41e05:	mov    DWORD PTR [rsp+0x38],r8d
   41e0a:	mov    r8d,r15d
   41e0d:	shr    r8d,0xa
   41e11:	mov    r9,r12
   41e14:	mov    ebp,r9d
   41e17:	rol    ebp,0x19
   41e1a:	mov    DWORD PTR [rsp+0xb8],ebp
   41e21:	xor    r8d,eax
   41e24:	mov    eax,r13d
   41e27:	rol    eax,0xe
   41e2a:	mov    ebp,eax
   41e2c:	add    ecx,r13d
   41e2f:	mov    eax,ebx
   41e31:	rol    eax,0xe
   41e34:	mov    ebx,eax
   41e36:	add    r8d,ecx
   41e39:	mov    QWORD PTR [rsp+0x80],r8
   41e41:	mov    eax,esi
   41e43:	rol    eax,0xe
   41e46:	mov    ecx,eax
   41e48:	xor    edx,r14d
   41e4b:	mov    esi,r9d
   41e4e:	rol    esi,0xe
   41e51:	mov    rax,QWORD PTR [rsp+0x50]
   41e56:	xor    eax,edx
   41e58:	mov    QWORD PTR [rsp+0x50],rax
   41e5d:	mov    eax,edi
   41e5f:	rol    eax,0x19
   41e62:	xor    ebp,DWORD PTR [rsp+0x68]
   41e66:	mov    DWORD PTR [rsp+0x68],ebp
   41e6a:	mov    r12,QWORD PTR [rsp+0x40]
   41e6f:	mov    r14d,r12d
   41e72:	rol    r14d,0x19
   41e76:	xor    ebx,DWORD PTR [rsp+0x78]
   41e7a:	mov    DWORD PTR [rsp+0x78],ebx
   41e7e:	mov    r8,QWORD PTR [rsp+0xa8]
   41e86:	mov    r9d,r8d
   41e89:	rol    r9d,0x19
   41e8d:	xor    ecx,DWORD PTR [rsp+0x38]
   41e91:	mov    DWORD PTR [rsp+0x38],ecx
   41e95:	mov    rcx,QWORD PTR [rsp+0x10]
   41e9a:	mov    ebx,ecx
   41e9c:	rol    ebx,0x19
   41e9f:	xor    esi,DWORD PTR [rsp+0xb8]
   41ea6:	mov    r13d,edi
   41ea9:	rol    r13d,0xe
   41ead:	xor    r13d,eax
   41eb0:	mov    edx,r12d
   41eb3:	rol    edx,0xe
   41eb6:	xor    edx,r14d
   41eb9:	mov    eax,r8d
   41ebc:	rol    eax,0xe
   41ebf:	xor    eax,r9d
   41ec2:	mov    r14d,ecx
   41ec5:	rol    r14d,0xe
   41ec9:	xor    r14d,ebx
   41ecc:	mov    ebp,DWORD PTR [rsp+0x8]
   41ed0:	add    ebp,edi
   41ed2:	add    DWORD PTR [rsp+0x98],edi
   41ed9:	shr    edi,0x3
   41edc:	xor    edi,r13d
   41edf:	mov    r9,rdi
   41ee2:	mov    rdi,QWORD PTR [rsp+0x20]
   41ee7:	add    edi,r12d
   41eea:	mov    QWORD PTR [rsp+0x20],rdi
   41eef:	mov    rdi,r12
   41ef2:	add    r9d,edi
   41ef5:	mov    QWORD PTR [rsp+0x8],r9
   41efa:	shr    edi,0x3
   41efd:	xor    edi,edx
   41eff:	mov    r13,QWORD PTR [rsp]
   41f03:	mov    rdx,r8
   41f06:	add    r13d,edx
   41f09:	add    edi,edx
   41f0b:	mov    QWORD PTR [rsp],rdi
   41f0f:	shr    edx,0x3
   41f12:	xor    edx,eax
   41f14:	mov    rax,rcx
   41f17:	mov    r12,QWORD PTR [rsp+0x48]
   41f1c:	add    r12d,eax
   41f1f:	add    edx,eax
   41f21:	mov    DWORD PTR [rsp+0x40],edx
   41f25:	shr    eax,0x3
   41f28:	xor    eax,r14d
   41f2b:	mov    ecx,DWORD PTR [rsp+0xb0]
   41f32:	add    eax,ecx
   41f34:	mov    QWORD PTR [rsp+0x10],rax
   41f39:	shr    ecx,0x3
   41f3c:	xor    ecx,DWORD PTR [rsp+0x68]
   41f40:	mov    rax,QWORD PTR [rsp+0x18]
   41f45:	add    ecx,eax
   41f47:	mov    DWORD PTR [rsp+0x48],ecx
   41f4b:	shr    eax,0x3
   41f4e:	xor    eax,DWORD PTR [rsp+0x78]
   41f52:	mov    rcx,QWORD PTR [rsp+0x28]
   41f57:	add    eax,ecx
   41f59:	mov    QWORD PTR [rsp+0x18],rax
   41f5e:	shr    ecx,0x3
   41f61:	xor    ecx,DWORD PTR [rsp+0x38]
   41f65:	mov    rax,QWORD PTR [rsp+0x60]
   41f6a:	add    ecx,eax
   41f6c:	mov    QWORD PTR [rsp+0x28],rcx
   41f71:	shr    eax,0x3
   41f74:	xor    eax,esi
   41f76:	add    eax,DWORD PTR [rsp+0x58]
   41f7a:	add    eax,r15d
   41f7d:	mov    QWORD PTR [rsp+0x60],rax
   41f82:	lea    eax,[r15+r11*1]
   41f86:	mov    rdx,QWORD PTR [rsp+0x70]
   41f8b:	mov    r9d,edx
   41f8e:	xor    r9d,r11d
   41f91:	and    r9d,r10d
   41f94:	xor    r9d,r11d
   41f97:	add    r9d,ebp
   41f9a:	mov    rcx,QWORD PTR [rsp+0x50]
   41f9f:	add    r9d,ecx
   41fa2:	add    r9d,0x19a4c116
   41fa9:	mov    rsi,QWORD PTR [rsp+0xa0]
   41fb1:	mov    r11d,esi
   41fb4:	rol    r11d,0x1e
   41fb8:	mov    ebp,esi
   41fba:	rol    ebp,0x13
   41fbd:	xor    ebp,r11d
   41fc0:	mov    r11d,esi
   41fc3:	rol    r11d,0xa
   41fc7:	xor    r11d,ebp
   41fca:	mov    r15,QWORD PTR [rsp+0xc0]
   41fd2:	mov    r14d,r15d
   41fd5:	mov    rbx,QWORD PTR [rsp+0xc8]
   41fdd:	xor    r14d,ebx
   41fe0:	and    r14d,esi
   41fe3:	mov    ebp,r15d
   41fe6:	and    ebp,ebx
   41fe8:	xor    ebp,r14d
   41feb:	add    ebp,r11d
   41fee:	add    ebp,r9d
   41ff1:	mov    edi,DWORD PTR [rsp+0x34]
   41ff5:	add    edi,r9d
   41ff8:	mov    r9d,edi
   41ffb:	rol    r9d,0x1a
   41fff:	mov    r11d,edi
   42002:	rol    r11d,0x15
   42006:	xor    r11d,r9d
   42009:	mov    r9d,edi
   4200c:	rol    r9d,0x7
   42010:	xor    r9d,r11d
   42013:	mov    r11d,r10d
   42016:	xor    r11d,edx
   42019:	and    r11d,edi
   4201c:	xor    r11d,edx
   4201f:	mov    rcx,rdx
   42022:	add    r11d,eax
   42025:	mov    eax,ebp
   42027:	rol    eax,0x1e
   4202a:	add    r9d,r11d
   4202d:	add    r9d,0x1e376c08
   42034:	mov    r11d,ebp
   42037:	rol    r11d,0x13
   4203b:	xor    r11d,eax
   4203e:	mov    eax,ebp
   42040:	rol    eax,0xa
   42043:	xor    eax,r11d
   42046:	mov    r11d,esi
   42049:	mov    rdx,r15
   4204c:	and    r11d,edx
   4204f:	mov    r15d,esi
   42052:	xor    r15d,edx
   42055:	and    r15d,ebp
   42058:	xor    r15d,r11d
   4205b:	add    r15d,eax
   4205e:	add    ebx,r9d
   42061:	mov    eax,ebx
   42063:	rol    eax,0x1a
   42066:	add    r15d,r9d
   42069:	mov    r9d,ebx
   4206c:	rol    r9d,0x15
   42070:	xor    r9d,eax
   42073:	mov    eax,ebx
   42075:	rol    eax,0x7
   42078:	xor    eax,r9d
   4207b:	mov    r8,QWORD PTR [rsp+0x88]
   42083:	mov    r11d,edi
   42086:	xor    r11d,r10d
   42089:	and    r11d,ebx
   4208c:	xor    r11d,r10d
   4208f:	add    r11d,r8d
   42092:	add    r11d,ecx
   42095:	add    eax,r11d
   42098:	add    eax,0x2748774c
   4209d:	mov    r9d,r15d
   420a0:	rol    r9d,0x1e
   420a4:	mov    r11d,r15d
   420a7:	rol    r11d,0x13
   420ab:	xor    r11d,r9d
   420ae:	mov    r9d,r15d
   420b1:	rol    r9d,0xa
   420b5:	xor    r9d,r11d
   420b8:	mov    r14d,ebp
   420bb:	xor    r14d,esi
   420be:	and    r14d,r15d
   420c1:	mov    r11d,ebp
   420c4:	and    r11d,esi
   420c7:	xor    r11d,r14d
   420ca:	add    r11d,r9d
   420cd:	add    r11d,eax
   420d0:	add    edx,eax
   420d2:	mov    eax,edx
   420d4:	rol    eax,0x1a
   420d7:	mov    r9d,edx
   420da:	rol    r9d,0x15
   420de:	xor    r9d,eax
   420e1:	mov    eax,edx
   420e3:	rol    eax,0x7
   420e6:	xor    eax,r9d
   420e9:	mov    rcx,QWORD PTR [rsp+0x80]
   420f1:	lea    r9d,[rcx+r10*1]
   420f5:	mov    r10d,ebx
   420f8:	xor    r10d,edi
   420fb:	and    r10d,edx
   420fe:	xor    r10d,edi
   42101:	add    r10d,r9d
   42104:	mov    r9d,r11d
   42107:	rol    r9d,0x1e
   4210b:	add    eax,r10d
   4210e:	add    eax,0x34b0bcb5
   42113:	mov    r10d,r11d
   42116:	rol    r10d,0x13
   4211a:	xor    r10d,r9d
   4211d:	mov    r9d,r11d
   42120:	rol    r9d,0xa
   42124:	xor    r9d,r10d
   42127:	mov    r14d,r15d
   4212a:	and    r14d,ebp
   4212d:	mov    r10d,r15d
   42130:	xor    r10d,ebp
   42133:	and    r10d,r11d
   42136:	xor    r10d,r14d
   42139:	add    r10d,r9d
   4213c:	add    r10d,eax
   4213f:	mov    r9d,r8d
   42142:	rol    r9d,0xf
   42146:	add    esi,eax
   42148:	mov    eax,r8d
   4214b:	rol    eax,0xd
   4214e:	xor    eax,r9d
   42151:	mov    r9,QWORD PTR [rsp+0x28]
   42156:	add    r9d,r8d
   42159:	mov    QWORD PTR [rsp+0x28],r9
   4215e:	mov    r9d,r8d
   42161:	shr    r9d,0xa
   42165:	xor    r9d,eax
   42168:	mov    eax,ecx
   4216a:	rol    eax,0xf
   4216d:	add    r9d,r12d
   42170:	mov    r14d,ecx
   42173:	rol    r14d,0xd
   42177:	xor    r14d,eax
   4217a:	mov    rax,QWORD PTR [rsp+0x18]
   4217f:	add    eax,ecx
   42181:	mov    QWORD PTR [rsp+0x18],rax
   42186:	mov    eax,ecx
   42188:	shr    eax,0xa
   4218b:	xor    eax,r14d
   4218e:	mov    r14d,r9d
   42191:	rol    r14d,0xf
   42195:	add    eax,r13d
   42198:	mov    r12d,r9d
   4219b:	rol    r12d,0xd
   4219f:	xor    r12d,r14d
   421a2:	add    edi,r9d
   421a5:	add    DWORD PTR [rsp+0x48],r9d
   421aa:	mov    r13d,r9d
   421ad:	shr    r13d,0xa
   421b1:	mov    r9d,eax
   421b4:	rol    r9d,0xf
   421b8:	xor    r13d,r12d
   421bb:	mov    r12d,eax
   421be:	rol    r12d,0xd
   421c2:	add    r13d,DWORD PTR [rsp+0x20]
   421c7:	xor    r12d,r9d
   421ca:	mov    r14d,eax
   421cd:	shr    r14d,0xa
   421d1:	xor    r14d,r12d
   421d4:	mov    r9d,esi
   421d7:	rol    r9d,0x1a
   421db:	add    r14d,DWORD PTR [rsp+0x98]
   421e3:	mov    r12d,esi
   421e6:	rol    r12d,0x15
   421ea:	xor    r12d,r9d
   421ed:	mov    r9d,esi
   421f0:	rol    r9d,0x7
   421f4:	xor    r9d,r12d
   421f7:	mov    rcx,QWORD PTR [rsp+0x10]
   421fc:	add    ecx,eax
   421fe:	mov    QWORD PTR [rsp+0x10],rcx
   42203:	add    eax,ebx
   42205:	mov    r12d,edx
   42208:	xor    r12d,ebx
   4220b:	and    r12d,esi
   4220e:	xor    r12d,ebx
   42211:	add    r12d,edi
   42214:	lea    edi,[r9+r12*1]
   42218:	add    edi,0x391c0cb3
   4221e:	mov    r8d,r10d
   42221:	rol    r8d,0x1e
   42225:	mov    r9d,r10d
   42228:	rol    r9d,0x13
   4222c:	xor    r9d,r8d
   4222f:	mov    r12d,r10d
   42232:	rol    r12d,0xa
   42236:	xor    r12d,r9d
   42239:	mov    r9d,r11d
   4223c:	xor    r9d,r15d
   4223f:	and    r9d,r10d
   42242:	mov    r8d,r11d
   42245:	and    r8d,r15d
   42248:	xor    r8d,r9d
   4224b:	add    r8d,r12d
   4224e:	add    r8d,edi
   42251:	add    ebp,edi
   42253:	mov    edi,ebp
   42255:	rol    edi,0x1a
   42258:	mov    r9d,ebp
   4225b:	rol    r9d,0x15
   4225f:	xor    r9d,edi
   42262:	mov    edi,ebp
   42264:	rol    edi,0x7
   42267:	xor    edi,r9d
   4226a:	mov    r9d,esi
   4226d:	xor    r9d,edx
   42270:	and    r9d,ebp
   42273:	xor    r9d,edx
   42276:	add    r9d,eax
   42279:	mov    eax,r8d
   4227c:	rol    eax,0x1e
   4227f:	add    edi,r9d
   42282:	add    edi,0x4ed8aa4a
   42288:	mov    r9d,r8d
   4228b:	rol    r9d,0x13
   4228f:	xor    r9d,eax
   42292:	mov    eax,r8d
   42295:	rol    eax,0xa
   42298:	xor    eax,r9d
   4229b:	mov    r9d,r10d
   4229e:	and    r9d,r11d
   422a1:	mov    ecx,r10d
   422a4:	xor    ecx,r11d
   422a7:	and    ecx,r8d
   422aa:	xor    ecx,r9d
   422ad:	add    ecx,eax
   422af:	add    r15d,edi
   422b2:	mov    eax,r15d
   422b5:	rol    eax,0x1a
   422b8:	add    ecx,edi
   422ba:	mov    edi,r15d
   422bd:	rol    edi,0x15
   422c0:	xor    edi,eax
   422c2:	mov    eax,r15d
   422c5:	rol    eax,0x7
   422c8:	xor    eax,edi
   422ca:	mov    r9d,ebp
   422cd:	xor    r9d,esi
   422d0:	and    r9d,r15d
   422d3:	xor    r9d,esi
   422d6:	add    r9d,r13d
   422d9:	add    r9d,edx
   422dc:	add    eax,r9d
   422df:	add    eax,0x5b9cca4f
   422e4:	mov    edi,ecx
   422e6:	rol    edi,0x1e
   422e9:	mov    r9d,ecx
   422ec:	rol    r9d,0x13
   422f0:	xor    r9d,edi
   422f3:	mov    r12d,ecx
   422f6:	rol    r12d,0xa
   422fa:	xor    r12d,r9d
   422fd:	mov    r9d,r8d
   42300:	xor    r9d,r10d
   42303:	and    r9d,ecx
   42306:	mov    edi,r8d
   42309:	and    edi,r10d
   4230c:	xor    edi,r9d
   4230f:	add    edi,r12d
   42312:	add    edi,eax
   42314:	add    r11d,eax
   42317:	mov    eax,r11d
   4231a:	rol    eax,0x1a
   4231d:	mov    r9d,r11d
   42320:	rol    r9d,0x15
   42324:	xor    r9d,eax
   42327:	mov    eax,r11d
   4232a:	rol    eax,0x7
   4232d:	xor    eax,r9d
   42330:	mov    r12d,r15d
   42333:	xor    r12d,ebp
   42336:	and    r12d,r11d
   42339:	xor    r12d,ebp
   4233c:	add    r12d,r14d
   4233f:	add    r12d,esi
   42342:	mov    r9d,edi
   42345:	rol    r9d,0x1e
   42349:	add    eax,r12d
   4234c:	add    eax,0x682e6ff3
   42351:	mov    r12d,edi
   42354:	rol    r12d,0x13
   42358:	xor    r12d,r9d
   4235b:	mov    r9d,edi
   4235e:	rol    r9d,0xa
   42362:	xor    r9d,r12d
   42365:	mov    esi,ecx
   42367:	and    esi,r8d
   4236a:	mov    r12d,ecx
   4236d:	xor    r12d,r8d
   42370:	and    r12d,edi
   42373:	xor    r12d,esi
   42376:	add    r12d,r9d
   42379:	add    r12d,eax
   4237c:	mov    esi,r13d
   4237f:	rol    esi,0xf
   42382:	add    r10d,eax
   42385:	mov    eax,r13d
   42388:	rol    eax,0xd
   4238b:	xor    eax,esi
   4238d:	mov    ebx,DWORD PTR [rsp+0x40]
   42391:	add    ebx,r13d
   42394:	mov    esi,r13d
   42397:	shr    esi,0xa
   4239a:	xor    esi,eax
   4239c:	mov    eax,r14d
   4239f:	rol    eax,0xf
   423a2:	add    esi,DWORD PTR [rsp+0x60]
   423a6:	mov    r9d,r14d
   423a9:	rol    r9d,0xd
   423ad:	xor    r9d,eax
   423b0:	mov    rax,QWORD PTR [rsp]
   423b4:	add    eax,r14d
   423b7:	mov    QWORD PTR [rsp],rax
   423bb:	mov    eax,r14d
   423be:	shr    eax,0xa
   423c1:	xor    eax,r9d
   423c4:	mov    r9d,esi
   423c7:	rol    r9d,0xf
   423cb:	add    eax,DWORD PTR [rsp+0x28]
   423cf:	mov    r14d,esi
   423d2:	rol    r14d,0xd
   423d6:	xor    r14d,r9d
   423d9:	add    ebp,esi
   423db:	mov    rdx,QWORD PTR [rsp+0x8]
   423e0:	add    edx,esi
   423e2:	mov    QWORD PTR [rsp+0x8],rdx
   423e7:	mov    r13d,esi
   423ea:	shr    r13d,0xa
   423ee:	mov    esi,eax
   423f0:	rol    esi,0xf
   423f3:	xor    r13d,r14d
   423f6:	mov    r9d,eax
   423f9:	rol    r9d,0xd
   423fd:	add    r13d,DWORD PTR [rsp+0x18]
   42402:	xor    r9d,esi
   42405:	mov    r14d,eax
   42408:	shr    r14d,0xa
   4240c:	xor    r14d,r9d
   4240f:	mov    esi,r10d
   42412:	rol    esi,0x1a
   42415:	add    r14d,DWORD PTR [rsp+0x48]
   4241a:	mov    edx,r10d
   4241d:	rol    edx,0x15
   42420:	xor    edx,esi
   42422:	mov    esi,r10d
   42425:	rol    esi,0x7
   42428:	xor    esi,edx
   4242a:	add    eax,r15d
   4242d:	mov    edx,r11d
   42430:	xor    edx,r15d
   42433:	and    edx,r10d
   42436:	xor    edx,r15d
   42439:	add    edx,ebp
   4243b:	add    edx,esi
   4243d:	add    edx,0x748f82ee
   42443:	mov    esi,r12d
   42446:	rol    esi,0x1e
   42449:	mov    r9d,r12d
   4244c:	rol    r9d,0x13
   42450:	xor    r9d,esi
   42453:	mov    esi,r12d
   42456:	rol    esi,0xa
   42459:	xor    esi,r9d
   4245c:	mov    ebp,edi
   4245e:	xor    ebp,ecx
   42460:	and    ebp,r12d
   42463:	mov    r9d,edi
   42466:	and    r9d,ecx
   42469:	xor    r9d,ebp
   4246c:	add    r9d,esi
   4246f:	add    r9d,edx
   42472:	add    r8d,edx
   42475:	mov    edx,r8d
   42478:	rol    edx,0x1a
   4247b:	mov    esi,r8d
   4247e:	rol    esi,0x15
   42481:	xor    esi,edx
   42483:	mov    edx,r8d
   42486:	rol    edx,0x7
   42489:	xor    edx,esi
   4248b:	mov    esi,r10d
   4248e:	xor    esi,r11d
   42491:	and    esi,r8d
   42494:	xor    esi,r11d
   42497:	add    esi,eax
   42499:	add    edx,esi
   4249b:	add    edx,0x78a5636f
   424a1:	mov    eax,r9d
   424a4:	rol    eax,0x1e
   424a7:	mov    esi,r9d
   424aa:	rol    esi,0x13
   424ad:	xor    esi,eax
   424af:	mov    ebp,r9d
   424b2:	rol    ebp,0xa
   424b5:	xor    ebp,esi
   424b7:	mov    esi,r12d
   424ba:	and    esi,edi
   424bc:	mov    eax,r12d
   424bf:	xor    eax,edi
   424c1:	and    eax,r9d
   424c4:	xor    eax,esi
   424c6:	add    eax,ebp
   424c8:	add    eax,edx
   424ca:	add    ecx,edx
   424cc:	mov    edx,ecx
   424ce:	rol    edx,0x1a
   424d1:	mov    esi,ecx
   424d3:	rol    esi,0x15
   424d6:	xor    esi,edx
   424d8:	mov    edx,ecx
   424da:	rol    edx,0x7
   424dd:	xor    edx,esi
   424df:	lea    esi,[r11+r13*1]
   424e3:	mov    r11d,r8d
   424e6:	xor    r11d,r10d
   424e9:	and    r11d,ecx
   424ec:	xor    r11d,r10d
   424ef:	mov    ebp,eax
   424f1:	rol    ebp,0x1e
   424f4:	add    r11d,esi
   424f7:	mov    esi,eax
   424f9:	rol    esi,0x13
   424fc:	add    edx,r11d
   424ff:	add    edx,0x84c87814
   42505:	mov    r15d,eax
   42508:	rol    r15d,0xa
   4250c:	xor    esi,ebp
   4250e:	xor    r15d,esi
   42511:	mov    esi,r9d
   42514:	xor    esi,r12d
   42517:	and    esi,eax
   42519:	mov    r11d,r9d
   4251c:	and    r11d,r12d
   4251f:	xor    r11d,esi
   42522:	add    edi,edx
   42524:	mov    esi,edi
   42526:	rol    esi,0x1a
   42529:	add    r11d,r15d
   4252c:	mov    ebp,edi
   4252e:	rol    ebp,0x15
   42531:	add    r11d,edx
   42534:	mov    edx,edi
   42536:	rol    edx,0x7
   42539:	xor    ebp,esi
   4253b:	xor    edx,ebp
   4253d:	lea    esi,[r14+r10*1]
   42541:	mov    r10d,ecx
   42544:	xor    r10d,r8d
   42547:	and    r10d,edi
   4254a:	xor    r10d,r8d
   4254d:	add    r10d,esi
   42550:	add    edx,r10d
   42553:	add    edx,0x8cc70208
   42559:	mov    esi,r11d
   4255c:	rol    esi,0x1e
   4255f:	mov    r10d,r11d
   42562:	rol    r10d,0x13
   42566:	xor    r10d,esi
   42569:	mov    esi,r11d
   4256c:	rol    esi,0xa
   4256f:	xor    esi,r10d
   42572:	mov    ebp,eax
   42574:	and    ebp,r9d
   42577:	mov    r10d,eax
   4257a:	xor    r10d,r9d
   4257d:	and    r10d,r11d
   42580:	xor    r10d,ebp
   42583:	add    r10d,esi
   42586:	add    r10d,edx
   42589:	add    r12d,edx
   4258c:	mov    edx,r13d
   4258f:	rol    edx,0xf
   42592:	mov    esi,r13d
   42595:	rol    esi,0xd
   42598:	xor    esi,edx
   4259a:	shr    r13d,0xa
   4259e:	mov    edx,r14d
   425a1:	rol    edx,0xf
   425a4:	xor    r13d,esi
   425a7:	mov    esi,r14d
   425aa:	rol    esi,0xd
   425ad:	add    r13d,DWORD PTR [rsp+0x10]
   425b2:	xor    esi,edx
   425b4:	shr    r14d,0xa
   425b8:	xor    r14d,esi
   425bb:	add    r14d,ebx
   425be:	mov    edx,r13d
   425c1:	rol    edx,0xf
   425c4:	mov    esi,r13d
   425c7:	rol    esi,0xd
   425ca:	xor    esi,edx
   425cc:	mov    edx,r14d
   425cf:	rol    edx,0xf
   425d2:	mov    r15d,r13d
   425d5:	shr    r15d,0xa
   425d9:	mov    ebp,r14d
   425dc:	rol    ebp,0xd
   425df:	xor    r15d,esi
   425e2:	xor    ebp,edx
   425e4:	mov    esi,r14d
   425e7:	shr    esi,0xa
   425ea:	xor    esi,ebp
   425ec:	mov    edx,r12d
   425ef:	rol    edx,0x1a
   425f2:	add    r13d,r8d
   425f5:	mov    r8d,r12d
   425f8:	rol    r8d,0x15
   425fc:	xor    r8d,edx
   425ff:	mov    edx,r12d
   42602:	rol    edx,0x7
   42605:	xor    edx,r8d
   42608:	add    r14d,ecx
   4260b:	mov    r8d,edi
   4260e:	xor    r8d,ecx
   42611:	and    r8d,r12d
   42614:	xor    r8d,ecx
   42617:	add    r8d,r13d
   4261a:	lea    ecx,[rdx+r8*1]
   4261e:	add    ecx,0x90befffa
   42624:	mov    edx,r10d
   42627:	rol    edx,0x1e
   4262a:	mov    r8d,r10d
   4262d:	rol    r8d,0x13
   42631:	xor    r8d,edx
   42634:	mov    ebp,r10d
   42637:	rol    ebp,0xa
   4263a:	xor    ebp,r8d
   4263d:	mov    r8d,r11d
   42640:	xor    r8d,eax
   42643:	and    r8d,r10d
   42646:	mov    edx,r11d
   42649:	and    edx,eax
   4264b:	xor    edx,r8d
   4264e:	add    edx,ebp
   42650:	add    edx,ecx
   42652:	add    r9d,ecx
   42655:	mov    ecx,r9d
   42658:	rol    ecx,0x1a
   4265b:	mov    r8d,r9d
   4265e:	rol    r8d,0x15
   42662:	xor    r8d,ecx
   42665:	mov    ecx,r9d
   42668:	rol    ecx,0x7
   4266b:	xor    ecx,r8d
   4266e:	mov    r8d,r12d
   42671:	xor    r8d,edi
   42674:	and    r8d,r9d
   42677:	xor    r8d,edi
   4267a:	add    r8d,r14d
   4267d:	add    ecx,r8d
   42680:	add    ecx,0xa4506ceb
   42686:	mov    r8d,edx
   42689:	rol    r8d,0x1e
   4268d:	mov    ebp,edx
   4268f:	rol    ebp,0x13
   42692:	xor    ebp,r8d
   42695:	mov    r14d,edx
   42698:	rol    r14d,0xa
   4269c:	xor    r14d,ebp
   4269f:	mov    ebp,r10d
   426a2:	and    ebp,r11d
   426a5:	mov    r8d,r10d
   426a8:	xor    r8d,r11d
   426ab:	and    r8d,edx
   426ae:	xor    r8d,ebp
   426b1:	add    r8d,r14d
   426b4:	add    r8d,ecx
   426b7:	add    eax,ecx
   426b9:	mov    ecx,eax
   426bb:	rol    ecx,0x1a
   426be:	mov    ebp,eax
   426c0:	rol    ebp,0x15
   426c3:	xor    ebp,ecx
   426c5:	mov    ecx,eax
   426c7:	rol    ecx,0x7
   426ca:	xor    ecx,ebp
   426cc:	mov    rbx,QWORD PTR [rsp]
   426d0:	add    ebx,r15d
   426d3:	add    ebx,edi
   426d5:	mov    edi,r9d
   426d8:	xor    edi,r12d
   426db:	and    edi,eax
   426dd:	xor    edi,r12d
   426e0:	add    ebx,edi
   426e2:	lea    edi,[rcx+rbx*1]
   426e5:	add    edi,0xbef9a3f7
   426eb:	mov    ecx,r8d
   426ee:	rol    ecx,0x1e
   426f1:	mov    ebx,r8d
   426f4:	rol    ebx,0x13
   426f7:	xor    ebx,ecx
   426f9:	mov    ebp,r8d
   426fc:	rol    ebp,0xa
   426ff:	xor    ebp,ebx
   42701:	mov    ebx,edx
   42703:	xor    ebx,r10d
   42706:	and    ebx,r8d
   42709:	mov    ecx,edx
   4270b:	and    ecx,r10d
   4270e:	xor    ecx,ebx
   42710:	add    ecx,ebp
   42712:	add    ecx,edi
   42714:	add    r11d,edi
   42717:	mov    edi,r11d
   4271a:	rol    edi,0x1a
   4271d:	mov    ebx,r11d
   42720:	rol    ebx,0x15
   42723:	xor    ebx,edi
   42725:	mov    edi,r11d
   42728:	rol    edi,0x7
   4272b:	xor    edi,ebx
   4272d:	mov    rbx,QWORD PTR [rsp+0x8]
   42732:	add    ebx,esi
   42734:	add    ebx,r12d
   42737:	mov    r14,rbx
   4273a:	mov    esi,eax
   4273c:	xor    esi,r9d
   4273f:	and    esi,r11d
   42742:	xor    esi,r9d
   42745:	mov    ebx,ecx
   42747:	rol    ebx,0x1e
   4274a:	add    r14d,esi
   4274d:	mov    ebp,ecx
   4274f:	rol    ebp,0x13
   42752:	lea    esi,[rdi+r14*1]
   42756:	add    esi,0xc67178f2
   4275c:	mov    r14d,ecx
   4275f:	rol    r14d,0xa
   42763:	xor    ebp,ebx
   42765:	xor    r14d,ebp
   42768:	mov    ebx,r8d
   4276b:	and    ebx,edx
   4276d:	mov    edi,r8d
   42770:	xor    edi,edx
   42772:	and    edi,ecx
   42774:	xor    edi,ebx
   42776:	add    edi,DWORD PTR [rsp+0x118]
   4277d:	add    edi,r14d
   42780:	add    ecx,DWORD PTR [rsp+0x120]
   42787:	add    edi,esi
   42789:	add    r8d,DWORD PTR [rsp+0xd0]
   42791:	add    edx,DWORD PTR [rsp+0xd8]
   42798:	add    r10d,DWORD PTR [rsp+0x130]
   427a0:	add    r10d,esi
   427a3:	add    r11d,DWORD PTR [rsp+0x128]
   427ab:	add    eax,DWORD PTR [rsp+0x110]
   427b2:	add    DWORD PTR [rsp+0xe4],r9d
   427ba:	mov    r9d,DWORD PTR [rsp+0xe4]
   427c2:	mov    rsi,QWORD PTR [rsp+0x100]
   427ca:	add    rsi,0x40
   427ce:	mov    r12d,edi
   427d1:	mov    r14d,ecx
   427d4:	mov    ebx,r8d
   427d7:	mov    QWORD PTR [rsp+0xd0],rbx
   427df:	mov    ebx,edx
   427e1:	mov    QWORD PTR [rsp+0xd8],rbx
   427e9:	mov    ebp,r10d
   427ec:	mov    r13d,r11d
   427ef:	mov    r15d,eax
   427f2:	mov    rbx,rsi
   427f5:	cmp    rsi,QWORD PTR [rsp+0x108]
   427fd:	jne    3fd00 <sha2::sha256::compress256+0x90>
   42803:	jmp    42829 <sha2::sha256::compress256+0x2bb9>
   42805:	mov    eax,r15d
   42808:	mov    r11d,r13d
   4280b:	mov    r10d,ebp
   4280e:	mov    rcx,QWORD PTR [rsp+0xd8]
   42816:	mov    edx,ecx
   42818:	mov    rcx,QWORD PTR [rsp+0xd0]
   42820:	mov    r8d,ecx
   42823:	mov    ecx,r14d
   42826:	mov    edi,r12d
   42829:	mov    rsi,QWORD PTR [rsp+0xe8]
   42831:	mov    DWORD PTR [rsi],edi
   42833:	mov    DWORD PTR [rsi+0x4],ecx
   42836:	mov    DWORD PTR [rsi+0x8],r8d
   4283a:	mov    DWORD PTR [rsi+0xc],edx
   4283d:	mov    DWORD PTR [rsi+0x10],r10d
   42841:	mov    DWORD PTR [rsi+0x14],r11d
   42845:	mov    DWORD PTR [rsi+0x18],eax
   42848:	mov    DWORD PTR [rsi+0x1c],r9d
   4284c:	add    rsp,0x138
   42853:	pop    rbx
   42854:	pop    r12
   42856:	pop    r13
   42858:	pop    r14
   4285a:	pop    r15
   4285c:	pop    rbp
   4285d:	ret
   4285e:	mov    r14,rdx
   42861:	call   428a0 <sha2::sha256::x86::shani_cpuid::init_get::init_inner>
   42866:	mov    rdx,r14
   42869:	test   al,al
   4286b:	je     3fca9 <sha2::sha256::compress256+0x39>
   42871:	mov    rdi,QWORD PTR [rsp+0xe8]
   42879:	mov    rsi,rbx
   4287c:	add    rsp,0x138
   42883:	pop    rbx
   42884:	pop    r12
   42886:	pop    r13
   42888:	pop    r14
   4288a:	pop    r15
   4288c:	pop    rbp
   4288d:	jmp    428f0 <sha2::sha256::x86::digest_blocks>
   42892:	int3
   42893:	int3
   42894:	int3
   42895:	int3
   42896:	int3
   42897:	int3
   42898:	int3
   42899:	int3
   4289a:	int3
   4289b:	int3
   4289c:	int3
   4289d:	int3
   4289e:	int3
   4289f:	int3

00000000000428f0 <sha2::sha256::x86::digest_blocks>:
   428f0:	movdqu xmm0,XMMWORD PTR [rdi]
   428f4:	movdqu xmm1,XMMWORD PTR [rdi+0x10]
   428f9:	pshufd xmm0,xmm0,0xb1
   428fe:	pshufd xmm12,xmm1,0x1b
   42904:	movdqa xmm13,xmm0
   42909:	palignr xmm13,xmm12,0x8
   42910:	pblendw xmm12,xmm0,0xf0
   42917:	test   rdx,rdx
   4291a:	je     42c86 <sha2::sha256::x86::digest_blocks+0x396>
   42920:	shl    rdx,0x6
   42924:	add    rdx,rsi
   42927:	movdqa xmm5,XMMWORD PTR [rip+0xfffffffffffd6911]        # 19240 <GCC_except_table365+0x3b4>
   4292f:	movdqa xmm9,XMMWORD PTR [rip+0xfffffffffffd6628]        # 18f60 <GCC_except_table365+0xd4>
   42938:	movdqa xmm10,XMMWORD PTR [rip+0xfffffffffffd675f]        # 190a0 <GCC_except_table365+0x214>
   42941:	movdqa xmm11,XMMWORD PTR [rip+0xfffffffffffd66c6]        # 19010 <GCC_except_table365+0x184>
   4294a:	nop    WORD PTR [rax+rax*1+0x0]
   42950:	movdqu xmm7,XMMWORD PTR [rsi]
   42954:	movdqu xmm14,XMMWORD PTR [rsi+0x10]
   4295a:	movdqu xmm2,XMMWORD PTR [rsi+0x20]
   4295f:	pshufb xmm7,xmm5
   42964:	pshufb xmm14,xmm5
   4296a:	movdqa xmm0,xmm7
   4296e:	paddd  xmm0,XMMWORD PTR [rip+0xfffffffffffd664a]        # 18fc0 <GCC_except_table365+0x134>
   42976:	movdqa xmm3,xmm12
   4297b:	sha256rnds2 xmm3,xmm13,xmm0
   42980:	pshufd xmm0,xmm0,0xe
   42985:	movdqa xmm4,xmm13
   4298a:	sha256rnds2 xmm4,xmm3,xmm0
   4298e:	movdqa xmm0,xmm14
   42993:	paddd  xmm0,XMMWORD PTR [rip+0xfffffffffffd6555]        # 18ef0 <GCC_except_table365+0x64>
   4299b:	pshufb xmm2,xmm5
   429a0:	sha256rnds2 xmm3,xmm4,xmm0
   429a4:	pshufd xmm0,xmm0,0xe
   429a9:	sha256rnds2 xmm4,xmm3,xmm0
   429ad:	movdqa xmm0,xmm2
   429b1:	paddd  xmm0,XMMWORD PTR [rip+0xfffffffffffd6767]        # 19120 <GCC_except_table365+0x294>
   429b9:	movdqu xmm8,XMMWORD PTR [rsi+0x30]
   429bf:	sha256rnds2 xmm3,xmm4,xmm0
   429c3:	pshufd xmm0,xmm0,0xe
   429c8:	pshufb xmm8,xmm5
   429ce:	sha256rnds2 xmm4,xmm3,xmm0
   429d2:	movdqa xmm0,xmm8
   429d7:	paddd  xmm0,XMMWORD PTR [rip+0xfffffffffffd6961]        # 19340 <GCC_except_table365+0x4b4>
   429df:	pshufd xmm1,xmm0,0xe
   429e4:	sha256msg1 xmm7,xmm14
   429e9:	sha256rnds2 xmm3,xmm4,xmm0
   429ed:	movdqa xmm6,xmm8
   429f2:	palignr xmm6,xmm2,0x4
   429f8:	movdqa xmm0,xmm1
   429fc:	sha256rnds2 xmm4,xmm3,xmm0
   42a00:	paddd  xmm6,xmm7
   42a04:	sha256msg2 xmm6,xmm8
   42a09:	movdqa xmm0,xmm6
   42a0d:	paddd  xmm0,XMMWORD PTR [rip+0xfffffffffffd67fb]        # 19210 <GCC_except_table365+0x384>
   42a15:	pshufd xmm1,xmm0,0xe
   42a1a:	sha256msg1 xmm14,xmm2
   42a1f:	sha256rnds2 xmm3,xmm4,xmm0
   42a23:	movdqa xmm7,xmm6
   42a27:	palignr xmm7,xmm8,0x4
   42a2e:	movdqa xmm0,xmm1
   42a32:	sha256rnds2 xmm4,xmm3,xmm0
   42a36:	paddd  xmm7,xmm14
   42a3b:	sha256msg2 xmm7,xmm6
   42a3f:	movdqa xmm0,xmm7
   42a43:	paddd  xmm0,XMMWORD PTR [rip+0xfffffffffffd6905]        # 19350 <GCC_except_table365+0x4c4>
   42a4b:	pshufd xmm1,xmm0,0xe
   42a50:	sha256msg1 xmm2,xmm8
   42a55:	sha256rnds2 xmm3,xmm4,xmm0
   42a59:	movdqa xmm15,xmm7
   42a5e:	palignr xmm15,xmm6,0x4
   42a65:	movdqa xmm0,xmm1
   42a69:	sha256rnds2 xmm4,xmm3,xmm0
   42a6d:	paddd  xmm15,xmm2
   42a72:	sha256msg2 xmm15,xmm7
   42a77:	movdqa xmm0,xmm15
   42a7c:	paddd  xmm0,XMMWORD PTR [rip+0xfffffffffffd66ac]        # 19130 <GCC_except_table365+0x2a4>
   42a84:	sha256rnds2 xmm3,xmm4,xmm0
   42a88:	sha256msg1 xmm8,xmm6
   42a8d:	movdqa xmm2,xmm15
   42a92:	palignr xmm2,xmm7,0x4
   42a98:	paddd  xmm2,xmm8
   42a9d:	sha256msg2 xmm2,xmm15
   42aa2:	pshufd xmm0,xmm0,0xe
   42aa7:	movdqa xmm8,xmm2
   42aac:	paddd  xmm8,XMMWORD PTR [rip+0xfffffffffffd66eb]        # 191a0 <GCC_except_table365+0x314>
   42ab5:	sha256rnds2 xmm4,xmm3,xmm0
   42ab9:	movdqa xmm0,xmm8
   42abe:	sha256rnds2 xmm3,xmm4,xmm0
   42ac2:	sha256msg1 xmm6,xmm7
   42ac6:	movdqa xmm1,xmm2
   42aca:	palignr xmm1,xmm15,0x4
   42ad1:	paddd  xmm1,xmm6
   42ad5:	sha256msg2 xmm1,xmm2
   42ad9:	pshufd xmm0,xmm8,0xe
   42adf:	movdqa xmm6,xmm1
   42ae3:	paddd  xmm6,XMMWORD PTR [rip+0xfffffffffffd67d5]        # 192c0 <GCC_except_table365+0x434>
   42aeb:	sha256rnds2 xmm4,xmm3,xmm0
   42aef:	movdqa xmm0,xmm6
   42af3:	sha256rnds2 xmm3,xmm4,xmm0
   42af7:	sha256msg1 xmm7,xmm15
   42afc:	movdqa xmm14,xmm1
   42b01:	palignr xmm14,xmm2,0x4
   42b08:	paddd  xmm14,xmm7
   42b0d:	sha256msg2 xmm14,xmm1
   42b12:	pshufd xmm0,xmm6,0xe
   42b17:	movdqa xmm6,xmm14
   42b1c:	sha256msg1 xmm15,xmm2
   42b21:	sha256rnds2 xmm4,xmm3,xmm0
   42b25:	movdqa xmm7,xmm14
   42b2a:	palignr xmm7,xmm1,0x4
   42b30:	paddd  xmm7,xmm15
   42b35:	paddd  xmm6,XMMWORD PTR [rip+0xfffffffffffd6673]        # 191b0 <GCC_except_table365+0x324>
   42b3d:	pshufd xmm15,xmm6,0xe
   42b43:	sha256msg2 xmm7,xmm14
   42b48:	movdqa xmm0,xmm6
   42b4c:	sha256rnds2 xmm3,xmm4,xmm0
   42b50:	sha256msg1 xmm2,xmm1
   42b54:	movdqa xmm6,xmm7
   42b58:	palignr xmm6,xmm14,0x4
   42b5f:	paddd  xmm6,xmm2
   42b63:	movdqa xmm2,xmm7
   42b67:	paddd  xmm2,XMMWORD PTR [rip+0xfffffffffffd6491]        # 19000 <GCC_except_table365+0x174>
   42b6f:	movdqa xmm0,xmm15
   42b74:	sha256rnds2 xmm4,xmm3,xmm0
   42b78:	sha256msg2 xmm6,xmm7
   42b7c:	sha256msg1 xmm1,xmm14
   42b81:	movdqa xmm0,xmm2
   42b85:	sha256rnds2 xmm3,xmm4,xmm0
   42b89:	movdqa xmm8,xmm6
   42b8e:	palignr xmm8,xmm7,0x4
   42b95:	paddd  xmm8,xmm1
   42b9a:	pshufd xmm0,xmm2,0xe
   42b9f:	movdqa xmm1,xmm6
   42ba3:	paddd  xmm1,XMMWORD PTR [rip+0xfffffffffffd6425]        # 18fd0 <GCC_except_table365+0x144>
   42bab:	sha256rnds2 xmm4,xmm3,xmm0
   42baf:	sha256msg2 xmm8,xmm6
   42bb4:	sha256msg1 xmm14,xmm7
   42bb9:	movdqa xmm0,xmm1
   42bbd:	sha256rnds2 xmm3,xmm4,xmm0
   42bc1:	movdqa xmm2,xmm8
   42bc6:	palignr xmm2,xmm6,0x4
   42bcc:	paddd  xmm2,xmm14
   42bd1:	pshufd xmm0,xmm1,0xe
   42bd6:	sha256msg2 xmm2,xmm8
   42bdb:	sha256msg1 xmm7,xmm6
   42bdf:	sha256rnds2 xmm4,xmm3,xmm0
   42be3:	movdqa xmm14,xmm2
   42be8:	palignr xmm14,xmm8,0x4
   42bef:	sha256msg1 xmm6,xmm8
   42bf4:	movdqa xmm0,xmm8
   42bf9:	paddd  xmm0,XMMWORD PTR [rip+0xfffffffffffd648f]        # 19090 <GCC_except_table365+0x204>
   42c01:	sha256rnds2 xmm3,xmm4,xmm0
   42c05:	pshufd xmm0,xmm0,0xe
   42c0a:	paddd  xmm14,xmm7
   42c0f:	sha256msg2 xmm14,xmm2
   42c14:	sha256rnds2 xmm4,xmm3,xmm0
   42c18:	movdqa xmm1,xmm14
   42c1d:	palignr xmm1,xmm2,0x4
   42c23:	movdqa xmm0,xmm2
   42c27:	paddd  xmm0,xmm9
   42c2c:	sha256rnds2 xmm3,xmm4,xmm0
   42c30:	pshufd xmm0,xmm0,0xe
   42c35:	sha256rnds2 xmm4,xmm3,xmm0
   42c39:	paddd  xmm1,xmm6
   42c3d:	sha256msg2 xmm1,xmm14
   42c42:	movdqa xmm0,xmm14
   42c47:	paddd  xmm0,xmm10
   42c4c:	sha256rnds2 xmm3,xmm4,xmm0
   42c50:	pshufd xmm0,xmm0,0xe
   42c55:	sha256rnds2 xmm4,xmm3,xmm0
   42c59:	paddd  xmm1,xmm11
   42c5e:	movdqa xmm0,xmm1
   42c62:	sha256rnds2 xmm3,xmm4,xmm0
   42c66:	pshufd xmm0,xmm1,0xe
   42c6b:	sha256rnds2 xmm4,xmm3,xmm0
   42c6f:	paddd  xmm13,xmm4
   42c74:	paddd  xmm12,xmm3
   42c79:	add    rsi,0x40
   42c7d:	cmp    rsi,rdx
   42c80:	jne    42950 <sha2::sha256::x86::digest_blocks+0x60>
   42c86:	pshufd xmm0,xmm13,0x1b
   42c8c:	pshufd xmm1,xmm12,0xb1
   42c92:	movdqa xmm2,xmm0
   42c96:	pblendw xmm2,xmm1,0xf0
   42c9c:	palignr xmm1,xmm0,0x8
   42ca2:	movdqu XMMWORD PTR [rdi],xmm2
   42ca6:	movdqu XMMWORD PTR [rdi+0x10],xmm1
   42cab:	ret
   42cac:	int3
   42cad:	int3
   42cae:	int3
   42caf:	int3
