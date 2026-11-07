# PCH-F1: required compiler differs from the frozen ELF compiler

Authority gate BLOCKED. No security defect or execution reachability claim.

Ruling (c-g)(2)(a) and this job require rustc 1.94.1 for SBF tied to the frozen Pool ELF.
NKZ_DEPLOYED_BUILD.json pool_build.native_rustc_version records host rustc 1.94.1.
However NKZ_aspis_pool.command.json selects
/home/dombarker/.rustup/toolchains/1.89.0-sbpf-solana-v1.52/bin/rustc.
The selected binary SHA-256 d95c95b68e321ad76634e1fd26b0a7c20ccdbae9ad9ca733f3ae2f2b4a0b6002
matches the retained build tool pin and reports rustc 1.89.0-dev / LLVM 20.1.7.
Its target is sbpf-solana-solana. The installed native 1.94.1 / LLVM 21.1.8
has bpfel/bpfeb targets but no sbpf-solana-solana target.
These targets and toolchains cannot silently be substituted.

The retained ELF receipt DOES match e0e49c344d35575116c0359450315ea4334bfb03006551727f67c04a8cfe09dc.
The source/lock comparisons pass. No fresh ELF was built or hashed.
Thus the blocker is the compiler/target requirement, not an observed ELF hash mismatch.
No evidence here demonstrates that a future compiler port cannot reproduce the hash;
no such port or toolchain installation is authorized by this audit.

Recommended lead action: reconcile (c-g)(2)(a)'s 1.94.1 requirement with the actual
pinned 1.89.0-dev SBF compiler, explicitly retaining the frozen ELF requirement,
or supply a matching 1.94.1 SBF toolchain and receipt. PCH makes no amendment.

Additional provenance caution: resolved_packages is cargo metadata, whereas
NKZ core's actual SBF command has no enabled feature cfg, statement has only
pool-v1-kernel, and Pool has the six recorded deployed features. PCH_AUTHORITY.json
records both separately. Metadata is not evidence that those cfg arms were emitted.

Shared bodies (Stream A): no per-body findings or status changes. The compiler
identity correction also applies when citing these retained core/statement artifacts.
No shared-body reachability assessment was attempted or duplicated.


## Round 2

PCH-F1 is RESOLVED by the lead compiler correction and the fresh B003 exact-ELF replay. PCH-F2: a resolved generic-template-to-instance association and full handler closure are not established by the three project MIR/IR modules. The compiler supergraph retains all such edges universally, so every row stays UNRESOLVED and no exclusion is proposed. Shared/verifier observations are routed in PCH_SHARED_FOR_STREAM_A.json (119 rows), never as exclusions.

PCH-F3 resource procedure: B004 was mistakenly launched while A006 was active; the own B004 scope was stopped immediately, receives no credit and consumes a build slot. The client now has an exclusive own-job guard. A006 was separately stopped at about 6.1 GiB process RSS to split serialization; A007 uses artifact locations/text hashes and streaming compressed JSON, rather than duplicating raw compiler text. No memory limit was raised and no memory-killed or timed-out shape was rerun.

Own-input errors retained: B001/A002 wrong ELF filename, A004 build.rs source mapping, A005 unqualified process_instruction MIR header. Repairs preserve or strengthen validation. The aborted local exploratory repeated-regex query was replaced by the artifact census and is not evidence.


PCH-F4: A018 uploaded the old three-control audit before the local strengthening edit. The serial client incorrectly hashed the mutable local script after execution, so its source hash drifted. The immutable PCH_A018_source.py upload snapshot and the three-control output are retained; PCH_ATTEMPTS.jsonl corrects the source hash explicitly and keeps the erroneous post-run hash. The client now hashes its uploaded text. The tested validator from A010–A014 is adopted; validate() is AST-identical to the A009 passing baseline. The later strengthening is retained as uncredited. A020 is a passing supplemental artifact audit on that later variant, not claimed as a mutation replay. No exclusion or status change relies on it.
