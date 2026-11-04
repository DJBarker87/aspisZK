# Frozen scanner comparison boundary

Status: OPEN; zero row/edge/root credit. Target not yet established.

The actual deployed comparison is not a Rust byte loop. In BOTH hash-checked
release ELFs the688-byte compare calls the wrapper at virtual address0x1749d0.
Its instruction0x1749e8 has an R_SBF_64_32 relocation to the undefined dynamic
symbol `sol_memcmp_`. The wrapper initializes a local i32 result to0, passes its
address in r4 while preserving r1/r2/r3, calls the runtime, reads that same slot,
sign-extends it and returns. The caller tests the low32 bits for zero.

Static scanner-shaped sites are0x4ab60 and0x50e48 (same addresses in default and
devnet): length guard0xe3b7=58295, compare size0x2b0=688, then tag at0x2b8=696
against2. They target0x1749d0 by the encoded PC-relative call. At0x4ab60,
r1=stack frame−0x568 (encoded reply),r2=r7 (retained header),r3=688;
at0x50e48,r1=the retained header andr2=stack frame−0x580. The ELF is stripped;
`custom_panic` printed as the nearest symbol is NOT the name of this wrapper or
scanner. The scanner source association follows its distinctive ordered guards
and buffer construction; a debug-symbol identity is not claimed. Another688-byte
comparison at0x48f78 belongs to a different-shaped continuation and is retained
in the inventory rather than silently counted as the scanner.

Pinned sysroot core/src/slice/cmp.rs selects SlicePartialEq's BytewiseEq path
for u8, checks matching lengths and invokes `intrinsics::compare_bytes` over
size_of_val(self), testing its reply against0. The pinned Solana compiler-builtins
mem/mod.rs defines memcmp with exactly this out-pointer syscall wrapper under
cfg(target_os="solana"). This is consistent with, and independently confirmed by,
the actual ELF relocation and instructions. The syscall BODY is absent from both
ELFs. A host Kani execution of core slice equality uses a different host/compiler
intrinsic path; no such pass certifies the missing deployed runtime body.

Rule15: frozen4bb3b3f51e16b4525f1d10336e2b0bcbbd775387;
lock5782e6a32026fdd95d252d0db7ea20b16716e6deb4f5a397e744886bb6ba22ef;
program pool-adapter,private-leaf-salts (default/custom-heap);
verifier default,private-leaf-salts,optimized-terminal,program-build;
core r0; statement r0,pool-v1-kernel and the twelve optimized features in
NCR_RELEASE_CFG.json/NCR_FEATURE_TABLE.md. sbpf-solana-solana release opt3,
platform-tools1.52/rustc1.89.0-dev/LLVM20.1.7. No no-entrypoint or profiling.
Exact build commands and default/devnet ID environment are retained. This is
inspection of existing release artifacts, not an SBF rebuild or Kani compilation.

## Smallest proposed trust item — NOT adopted

`RuntimeMemcmp688Zero`: for the SAME two valid readable688-byte ranges passed
at this call (allowing aliasing and arbitrary contents/alignment), sol_memcmp_
returns normally, writes its supplied i32 output slot, and writes zero iff all688
corresponding bytes are equal. It changes no input byte or other observable
state and emits no protocol/oracle event. No sign, magnitude, timing or
lexicographic ordering guarantee is needed. Runtime failure/abort must be
specified separately if the runtime admits it on the caller-established domain.

This would be ADDED runtime trust, requiring a lead/owner ruling. It is not
PhysicalInterpretation, P6 option-A reclassification, RuntimeSyscall's hash
realization, TrustedStd copying, RuntimeReturnData(ab), or a Lean-discharged field
stub. No approval is inferred here, and no certificate consumes it.

## Alternative outside-slice packet

Pin the deployed validator/runtime implementation, enabled runtime features and
memory translation/checking rules for sol_memcmp_. Extract its real bounded
iteration (including access errors and result-slot frame), prove one arbitrary
byte/window step with local records and matched controls, and compose its exact
zero law using NEU_EqualityLoop. Bind the syscall registry entry and memory mapping
to these release calls and retained input allocations. The runtime implementation
is outside slice S's function list: it cannot be silently replaced by a new Rust
reference loop inside scan_proof_buffer. No extra solver budget can make a body
absent from the ELF visible to a verifier-program Kani harness.

## Universal-interface caution

NFD_s NativeEqualityAssociation quantifies over ALL list lengths. A688-only
runtime contract must not be passed as that universal law verbatim. The accepted
NFH_ComparisonDomain.complete688_association provides a mathematical completion
off-domain, conditional on At688Law;complete688_on_domain proves its local
agreement. Native use still requires both SAME buffers to have length688.
This does not discharge At688Law or prove the actual runtime implementation.
