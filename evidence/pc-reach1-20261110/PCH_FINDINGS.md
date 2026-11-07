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
