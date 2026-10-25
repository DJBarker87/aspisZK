# Frozen native Prepared::new control and caller scratch identity

S1 and S6 remain OPEN. This packet checks one native constructor boundary;
it does not remove a hypothesis from the enclosing Lean SDK theorem. The
accepted Claims range premise removal remains the separate `cef39d839d`
result (`S1-ACCEPTED-CLAIMS-RANGES-20261025.md`). S2 ownership is transferred.
Here “S2 variant” means the protocol enum value, not ownership of the S2 cone.

## Exact result

The complete frozen `impl Prepared` is executed by Kani, with its complete
native `Verified<H>`, `View`, `Prepared` and release `Error` declarations.
Imports are factored into a two-package probe; no selected constructor body
or public carrier is rewritten. Frozen source revision:
`25866ec331cc7ce27dd9956609c11d32fa8fa58a`, including adopted early-return
powers `29cbab431742f7e899870595167efa193a379f0a`. The complete sibling
transport, fast_pairing, trace, transcript and r1_wire modules and all 88 core
source files are pinned. The source-only materializer records exact source
spans and complete source hashes. Two cfg(kani) state constructors and a proof
submodule are appended. This is not whole-crate, whole-context or ABI identity.

Target: `verifier::proofs::prepared_new_s2_control`.
Six child boundaries use normal-return stubs: Transcript::new, scalar,
queries, scalar_k, powers and prepared_claim. At each actual call, the stub
checks the expected stage, receiver state and arguments before supplying
arbitrary child outputs. No `kani::assume` or transmute is used.

The accepted final check establishes, on its input domain:

- Native scalar calls occur in order at rows 27–30; only row 27 requests a
  nonzero scalar. Their inputs are the original y1 bytes, inactive encoding,
  original round0 bytes, then the native folded-root/round1 concatenation.
- Queries receives row 31 and the original final-message slice. Rho receives
  row 32 and the empty payload. The native state chain follows the same
  child-return state tape.
- Powers receives the same row-27 gamma and N=29. The claim call receives the
  same complete semantic object, y1, inactive and row-28 kappa. Its `g` address
  is the EXACT caller-owned scratch array passed to Prepared::new, and all
  29 eight-word values equal the powers result installed by the constructor.
- Query errors return the exact error with incoming scratch unchanged.
  Claim errors return the exact error after the new powers have been stored.
- Success returns every native Prepared field: variant, roots, gamma, kappa,
  both alphas, rho, all 22 queries, all ten semantic alphas, both circle
  points, claim and final transcript state. No field is replaced by a
  simplified projection.

The final input domain makes every semantic field and every observed message
byte symbolic. Raw QM31 coordinates may be any u32. WideExact values range
over every canonical private-valid eight-word value, using its actual strict
from_limbs constructor; this is domain coverage, not a sampling-law claim.
The variant is S2, folded_root is present, and frame lengths are 928/224/224/
2048. View.semantic and query_bytes are empty because the selected constructor
never reads or passes them. This is not malformed-View or other-variant
coverage. Hash is a zero-sized test Digest32 whose digest panics outside the
cuts: arbitrary stateful hash clone/drop behavior and the actual SDK hash are
NOT established by this check.

## Validation and negative control

Kani 0.67.0, official aarch64-apple-darwin asset SHA256
`7fd0b71130aa37bd1e346eba675aad09e9b66e4b383f707fc657330ceb29eeec`;
rustc `1.93.0-nightly (53732d5e0 2025-11-20)`. All package/tool/host-sysroot
files are pre/post pinned in each input/receipt. Optimized Rust, overflow
checks enabled, unwind 257 with unwinding assertions, default Kani checks.
No uninit-checks or partial-loop options. Default malloc-success modeling
means this is NOT allocation-failure, initializedness, OOM/abort or cleanup
coverage. No new Lean theorem: `#print axioms` is N/A.

| Attempt | Target/result | Exit | Wall s | Peak RSS bytes | Sampled aggregate bytes | Swap |
|---|---|---:|---:|---:|---:|---:|
| v1 | initial compile | 0 | 1.143660 | 394854400 | 425639936 | 0 |
| v2 | initial positive: 0/1576 failed, 3/3 covers | 0 | 30.690782 | 1403322368 | 1814429696 | 0 |
| v3 | negative-control compile | 0 | 1.133293 | 394133504 | 406667264 | 0 |
| v4 | expected pointer assertion failure: 1/1576 | 1 | 16.672769 | 897859584 | 1136476160 | 0 |
| v5 | strengthened input-domain compile | 0 | 1.146900 | 396558336 | 418627584 | 0 |
| v6 | strengthened positive: 0/1582 failed, 3/3 covers | 0 | 28.404285 | 1434583040 | 1947516928 | 0 |

v6 is the accepted final positive result; v2 is superseded. v1–v4 fixed
unobserved metadata and most frame bytes. They are never relabeled as the
strengthened proof. The historical negative control changes only the expected
scratch address to the separate initial-array copy; v4 fails exactly
`g as *const [E;29] == G_PTR`. It demonstrates that the checked predicate
observes caller-array identity, rather than mere value equality. Its narrower
historical input domain and snapshots are retained. The current source also
contains the strengthened negative control; that version was not run.

Each local job held the shared atomic mkdir compiler lock and had a 2 GiB
sampled process-group RSS watchdog, 64-process bound and 180-second timeout.
These are ordinary focused Mac checks, NOT hard cgroup MemoryMax or no-swap
isolation. All stopped normally without watchdog termination; observed process
swaps were zero. No SSH, NUC work, cold dependencies or full replay ran.
Exact commands, source revision, snapshot hashes, timing, output, compiler and
solver binary pins are in each immutable attempt directory.

The source-only kit v3 exactly regenerates every snapshotted v6 source,
including Cargo.toml. Its 102 files are checked against the pre/post source
pins; core and sampler bytes are reconstructed from immutable Git blobs.
Earlier source kits v1/v2 were preparation artifacts only. The source origin
inventory is a post-run audit; contemporaneous input.json hashes and source
snapshots are the execution pins. Nothing retroactively repins old runs.

Read-only packet check:

```
python3 tools/s1-native-prepared-20261025/check.py
```

It checks 127 source/evidence hashes, source origins, all receipts, source/tool
stability, successful final counters, explicit child cuts and the excluded
negative control. The packet is focused-extractor-proof-packet-v1 and contains
no binaries. No frozen production source or release artifact changed.

## Exact residuals and next connection

This supplies native constructor control evidence to accompany the existing
Lean original/candidate Prepared transport and the native prepared_claim
word-control packet. Child normal-return coupling is still explicit. Native
sampler/digest/oracle semantics, powers arithmetic, prepared_claim arithmetic,
allocation/init/cleanup, original Std/FnMut/Terminal installation, actual SDK
Digest32 binding, coherent original/current kernel composition and release
artifact transport remain separate. In particular, the local result does not
instantiate Library/SDK/Std/allocator/FinishModel B or AeneasExtraction fields
of the enclosing caller theorem. No probability law is inferred from the
arbitrary tapes.

The next native connection is the actual SDK hash carrier at this constructor
boundary and the source-bound child coupling, followed by integration into the
same caller witness. The safe Claims storage candidate remains NOT ADOPTED;
its source-only extraction preparation has no build-host execution admission.
There is no required protocol or production-source decision from this packet.
S1/S6 and the overall <=2^-100 per-attempt target remain not yet established.
