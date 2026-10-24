# Port24SBFMAP: current selected implementation association

No deployed whole-helper binding is closed. This packet establishes new,
read-only associations to the **current** retained build artifacts, substantially
narrower than a general Vec specification. It adds no semantic or cryptographic
assumption, no theorem, and no shipped source change. Both security targets
remain **not yet established**.

## What is newly established

`selected-implementation.json` retains complete selected MIR/LLVM bodies, original
line intervals, body hashes, diagnostic compiler commands, frozen owned source
hashes, ELF section metadata, selected symbol addresses/sizes/machine hashes,
and raw allocator instruction records. `binding-map.json` lists each selected
LLVM definition separately, including **empty final-symbol matches**. An empty
match is not silently converted into an inline/native association.

The collector reads only the released S10 re-pin3 snapshot and retained build
artifacts. It does not enter live source trees, compiler/registry/build caches,
other worker directories, or session-A candidates. It executes no compiler,
disassembler downloaded from elsewhere, build, extraction, Rust or Lean gate.
Keys are neither opened nor changed. Python parses bounded ELF metadata and
selected text ranges; binaries are retained remotely and never committed.

56 inspected retained outputs match their S10 build-manifest hashes and sizes.
64 inputs in total are pinned; remaining inputs are classified source-manifest,
selected owned source, and diagnostic-command files. All seven selected owned
files also match this worktree. The original S10 source revision is
`4bb3b3f51e16b4525f1d10336e2b0bcbbd775387`; its harness's stale revision
field is retained in raw receipts and is not treated as source identity.

| Mode | Current deployed SHA-256 | Linked ELF SHA-256 |
|---|---|---|
| default | f8c0ec72621fd5029a97d796c4a3623d0dc44a8e7074122372f9872915d143d4 | 7bcef5f326203239ec867a91d68a5be027bde7e75ffa5adce259d182006562c2 |
| devnet | 63ad3e9cc096dcbb55b3ca7ac7c8e89e6a845796ab5e4f5b7d15db96f3784299 | 1e9d7e4b940c40e441a33ea06b5622824f2b0ed06160ce1803295def647cce36 |
| Pool | 121f3e29741f510e6dc42d0345fc3c36217600f0be337094855c4a9da2581548 | 8855cbbc25ff2f634767c3e4d0c3b8146d2077b07783d0254ebc8374d9e8dbf7 |

For each mode, independently parsed linked/deployed `.text` bytes agree.
Default/devnet text SHA-256 is
`f3684961bb5eff741ddea43167afd998d7e8276b4f50b13895a9e59f014fad0e`;
Pool is `d32a5d4472bd6d600e6d41e36dde05cb3be67a394eda769ba3445166e49f53d0`.
This confirms inspected text identity, not a whole-artifact semantics theorem.

## Toolchain and dependency identity: established versus missing

Every retained rustc diagnostic command selects
`/home/dombarker/.rustup/toolchains/1.89.0-sbpf-solana-v1.52/bin/rustc`,
target `sbpf-solana-solana`, optimization level 3, stripped debug information,
and emitted MIR/LLVM IR. LLVM text identifies `rustc version 1.89.0-dev`, target
triple `sbf`, data layout `e-m:e-p:64:64-i64:64-n32:64-S128`.
The linked ELF `.comment` identifies LLD 20.1.7 and anza-xyz/llvm-project
revision `78496716176191b2dfb728e5e38501812e7467db`.
Build commands select cargo-build-sbf in Solana release 3.1.13, offline/locked,
`--skip-tools-install`; default features are `pool-adapter,private-leaf-salts`.
Exact per-mode features, IDs and arguments are retained, not inferred.

The frozen Cargo.lock hash is
`5782e6a32026fdd95d252d0db7ea20b16716e6deb4f5a397e744886bb6ba22ef`.
Its selected solana-program / solana-program-entrypoint package versions and
registry checksums are extracted verbatim in `sources`. The lock pins package
archives; it is not proof of the source bytes actually loaded by rustc.

**Missing implementation identity:** these current receipts do not retain a
content digest of the compiler executable, selected `alloc`/`core` archives,
matching rust-src tree, or the defining Rust `Global`/RawVec source declarations.
The current owned-input manifest has 7,978 records and no extra workspace inputs;
it does not provide those sysroot files. Diagnostic executable paths and version
strings are observed selection evidence, not content hashes. No exact rustc
source commit can be recovered from `1.89.0-dev` alone. No current cache lookup
or install is used to manufacture historical build identity.

Consequently, the exact **emitted implementation** can be pinned below, while
an exact **Rust sysroot source declaration** pin remains missing. Port21/22's
nightly-2026-06-01 host alloc source and Kani's Rust1.93 sysroot are different;
none of their source statements or clone specializations is relabelled as
this SBF sysroot. Next identity producer: release/artifact custodian supplies an
already retained contemporaneous toolchain/sysroot hash receipt, archives and
matching source manifest, if one exists. Otherwise a newly authorized capture
would require explicit assessment against these historical builds; matching
version names alone would still be insufficient. No rebuild is requested here.

## Actual allocator selection and source membership

Owned `programs/r1-cost-probe/src/lib.rs` hash
`e56fd18185d72d5b925da56fdd168a05c9bfea2da1c2d17058d097f74c66d4d8`
contains the cfg-selected global BumpAllocator declaration with `len=256*1024`.
Retained program MIR's `fn __rust_alloc(usize,usize)->*mut u8` constructs the
actual Layout and calls `<BumpAllocator as GlobalAlloc>::alloc`; the complete
selected LLVM definition inlines that allocator body. Its cursor is at
`S=12884901888=0x300000000`, zero cursor selects end `S+262144`, saturation,
negative-align mask and threshold `S+8` are explicit, and only success stores
the cursor. This is actual emitted body inspection, beyond a package name.

Pool's source `processor.rs` hash
`a95ccc46e3083b539115fade0f88f1509635a2dbcff5b5b7d78bc42108ba2b83`
uses `solana_program::entrypoint!`. Its actual MIR/LLVM shim selects the same
allocator implementation with **32768 bytes**, end `S+32768`. The default/devnet
256 KiB arena must not be assigned to Pool. This difference is visible in final
machine bytes, not just macro interpretation.

Exact shim symbol in all modes:
`_RNvCscR3e5J6VSLN_7___rustc12___rust_alloc`.
Its signature is `ptr (i64 size, i64 align)`, hidden, with the exact LLVM
attributes retained in JSON. Default/devnet PC=334408, size=272 bytes,
machine hash `fd8c189f807b60d8afa272abdf33387ae25fc768f3e66ad1475025afea9f0f23`;
Pool PC=390432, size=272,
`9753b5553db6e77757e3e4d2cefdcee723e0b53654d5e399246b57ecc8231b39`.
The 34 instruction slots include long-immediate continuation slots. They
contain no call/callx opcode. This is a syntactic fact, not an installed
native no-oracle semantics theorem. The sole cursor-store instruction is at
shim+168 (default/devnet 334576; Pool 390600). Actual primitive semantics,
valid-address/provenance admission and ordered fault effects remain necessary.

`finish_grow` also calls the selected unstable allocation marker
`_RNvCscR3e5J6VSLN_7___rustc35___rust_no_alloc_shim_is_unstable_v2` before
`__rust_alloc`. The marker has an 8-byte final symbol; its semantics are not
inferred from its name. The allocator error handler is a separate 16-byte
symbol. Neither is silently omitted from the primitive/effect audit.

## Actual Vec/RawVec and content path

The unchanged `heap.rs` hash is
`67153a3fb69c839160855a9b8fdb886fbd1eac90f4dc686260f23a85e346e4f9`.
Its retained generic MIR shows the complete hidden construction:
`RawVecInner { ptr: Unique(...NonNull...alignment...), cap: ZERO_CAP,
alloc: const alloc::alloc::Global }`, `RawVec<T> { inner, PhantomData }`,
`Vec<T> { buf, len: 0 }`. It copies len by value, exclusively reborrows the
inner RawVec, and calls `RawVecInner::try_reserve_exact(self,len,n,T::LAYOUT)`.
This establishes the selected allocator value at the emitted MIR construction;
it does not recover the missing Rust declaration source bytes.

The selected emitted Core LLVM reserve specialization has signature:
`i64 (ptr self, i64 additional, i64 elem_layout_alignment, i64 elem_layout_size)`.
It has specialized len away; it is **not** an arbitrary-len reserve theorem.
It loads cap from `self+0`, compares additional, computes padded stride,
checks unsigned multiplication overflow and the `2^63-alignment` layout bound,
forms `current_memory=None` when cap=0, and calls `finish_grow`. Failure
branches skip header commits. Success stores ptr at `self+8`, **then** cap at
`self+0`. Its complete body is retained. This generic reserve definition has
no selected out-of-line final-symbol match; source-to-inline association is
still open. `finish_grow` does have exact symbol matches for listed instances.

In the selected `finish_grow` bodies, cap0's current-memory tag0 selects the
fresh allocate branch, not realloc; nonzero layout calls marker then shim.
Null is converted into the actual error discriminant in a temporary result.
Those temporary result stores still occur on failure: “no header commit” does
not mean “no memory changes”. The header and temporary-result objects must be
separately admitted. Zero additional bypasses allocation at reserve level.

`Accumulator::new` source hash
`8c872d42bdaa245cc540be6b26d17108a5cb40754b8befb79e147f5843b1f756`
contains `filled(v.final_len(),QM31::ZERO).map_err(...)`. Its retained MIR pins
the actual Variant branches: final lengths 256 or 64. Its emitted LLVM and
final symbol `_ZN19aspis_r1_cost_probe8verifier11Accumulator3new17h25f58530696f9377E`
(PC795840,408 bytes default/devnet) show one `finish_grow`, then 16-byte
initialization operations and result stores. No second growth call appears in
this emitted body. This is concrete progress toward this caller, not a generic
wrapper around an external reserve result.

The same verifier source's `BatchedWeights::new` calls `filled(weights.len(),
[0u64;4])`. Its exact emitted/final instance is
`_ZN19aspis_r1_cost_probe8verifier14BatchedWeights3new17hed5f78a6e058e253E`
(PC800992,704 bytes default/devnet). The body handles n=0, checked 32*n layout,
alignment8 and null failure; on success it initializes **all32 bytes** per
array before the subsequent row conversion. The n=1 branch and final move
are explicit. Subsequent conversion loads all four QM31 words and writes four
u64 limbs; a separate bounds-panic branch is retained, not erased by reporting.
There is no matching cost-probe caller/monomorphization in Pool's retained
outputs; emitted Core definitions in Pool are not promoted to live instances.

For nonzero literal filled specializations, complete LLVM loops show n-1
full-width copies and one final copy (16 bytes for QM31,32 for WideExact), or
full-width zero initialization for the two zero callers. **WideExact's 32-byte
align4 copy must not be mistaken for [u64;4]'s align8 initialization.**
`field.rs` hash `28df5a1abee13bde4b3aa9eeceb0489bedf00531f298460954a97661f5f1baea`
retains QM31's full Clone/Copy-derived source structure. No SBF array
`SpecArrayClone`/`TrivialClone` source law is borrowed from the newer host std.

The generic filled MIR pins literal map_err and `?`: reserve Err maps to
Core Allocation, drops fresh out, returns Err; Ok alone reaches resize and
moves the Vec. Accumulator's second map_err maps to verifier Allocation.
Complete MIR scopes/branches are retained, including the explicit error drop.
The emitted result layouts store a capacity/niche at result+0, pointer+8 and
length+16 on successful Vec-bearing results. These are **observed offsets of
these emitted results**, not Rust's promised generic Vec ABI. The source-level
logical field ordering differs: MIR names buf field0 and len field1. A concrete
source-field-to-address admission still needs to identify the reborrowed
RawVec/header and result/temporary objects; naming them does not prove it.

## Assumptions, stopped items, resources and handoff

No theorem statement/premise changed; before/after premise inventory is
identical. No whole-helper equality or nativeNoHash is assumed. P7 remains the
literal reviewed-source compilation boundary; D157's unsafe/allocation-failure
exclusion and D189/P2's account projection retain their original scope.
`PRIMITIVES.md` supplies exact small load/store/pointer/field/content targets,
ordered null/error/fault/abort prefixes, a derivation route, and a conditional
minimal boundary packet. This is a specification deliverable, not an adopted
trust extension. The first missing producer is contemporaneous sysroot source
identity, followed by the selected native memory/effect interpretation.

Rejected substitutions retained: host-nightly Global/array clone source is not
SBF sysroot identity; Kani's finite copied allocator is not this deployed arena;
Pool is not256KiB; 32-byte align4 WideExact is not [u64;4]; emitted generic
reserve without a final symbol/inline map is not a concrete native law; symbol
membership/no-call slots alone do not establish ABI semantics/oracle effects.
Early guessed source locations lacking `r0/` or the actual crate were absent;
the frozen manifest resolved them before any evidence claim. No proof attempt,
resource failure or counterexample was discarded; no Lean attempt was launched.

New validation is the read-only collector and 121 focused integrity checks,
with commands, exit0, wall/RSS/swap, script/source/dependency hashes and N/A
axioms recorded. Final selected capture: host Python wall1.479253s,
peak207080KiB, swap0; local SSH receipt separately records transport resources.
Read-only inspection remained far below8GiB. No host build process/scope,
reservation, lock, cold dependency build or heavy arithmetic job was launched;
build-only scope/aggregate reservation/Lean time-window gates are N/A.
Reused S10 build timings/resource caps and Port22 theorem/Kani receipts retain
historical scope; this job does not report them as new gates or rerun them.

Budget used: Lean0/7 carry, Kani0, extraction0, standaloneRust0, backend0,
ELF rebuild0, fullmanifest0. Global baseline remains at least332/368 charged,
with pending other jobs separate; Port23's unused7 and extraction carry are
untouched; unassigned22 unchanged. No seven-attempt spending is justified by
an unbound arithmetic wrapper. Lead may assign a source-identity custodian and
then the selected primitive producer; this packet is concrete enough to scope
that work without demanding entire SDK certification. No merge/push/production,
protocol, feature, wire, security-contract, key, service or chain mutation.
