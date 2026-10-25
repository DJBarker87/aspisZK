# Native constructor and actual transcript execution, 2026-10-25

S1/S6 and the implementation-linked 100-bit target remain open. This result
checks the original native constructor together with its complete transcript
bodies and gamma-powers body, under explicit primitive/sampling/claim cuts.
It does not remove the enclosing SDK extraction or SourceCuts premises.

## Exact change in the checked statement

Predecessor: commit 26990758ee, packet s1-native-prepared-powers-20261025.
Transcript::new/scalar/queries/scalar_k were normal-return cuts. The actual
constructor and powers::<29> already executed, with multiplication cut.

New harness: verifier::proofs::prepared_new_s2_native_transcript. All four
transcript cuts are removed. Complete frozen new, absorb, block, scalar,
queries and scalar_k bodies execute inside the same Prepared::new invocation.
A scripted Digest32 implementation checks the number, order, slice framing,
state bytes, domain tags and message bytes or original borrowed pointer/length
of every digest input. It supplies arbitrary symbolic 32-byte replies.

The new statement checks 33 digest calls on successful query selection (including
claim rejection) and 30 on query failure. All eight squeeze/advance pairs are
materialized before the query-sampler cut, including on failure. Each pair
uses the previous advance, starting with the row-31 absorbed state; the rho
absorption starts at the selected advance, which can precede the eighth.
The native error mapping produces Error::Transcript on query failure and
performs no rho digest, multiplication, or scratch write in that branch.

The four source scalar calls use the checked blocks at rows27–30, with gamma
sampling only at row27; rho uses row32's actual block. The same execution then
performs 28 gamma multiplications, builds all29 scratch entries starting at
ONE, and supplies the caller's actual scratch address/entries to prepared_claim.
Query/claim errors and the complete native Prepared return remain checked.

## Remaining cuts and domain

Six cuts remain: gamma_sample, ordinary_sample, qm31_sample,
queries_from_pairs, WideExact::mul, prepared_claim. Samples and arithmetic
results are symbolic normal returns; claim errors cover all release Error
variants. Query selection returns arbitrary query words and a selected one
of the eight actual advances, or a sampler error that the source maps to
Transcript. This is an overapproximation of the real sampler, not its proof.

Digest replies are a symbolic execution tape. Repeated preimages need not
have consistent replies in this harness. No concrete hash or oracle
probability/determinism transport is claimed. No native sampling arithmetic,
initializedness, allocation/cleanup, SDK/extraction/runtime/ABI or SBF join
is discharged. Fixed valid S2 View frame lengths/folded root and canonical
private WideExact carriers remain the predecessor domain. This is not
arbitrary-input TOTAL. Actual query rejection is covered, not just acceptance.

The existing Lean joint serialized-rank/query-program proofs and native claim
word checks are reused as separate evidence. This packet does not silently
install their concrete implementations into the SDK theorem or establish
cross-language/oracle transport by matching function names.

## Freeze and source evidence

Freeze 25866ec331cc7ce27dd9956609c11d32fa8fa58a, with the adopted early-return
powers overlay. All native payload modules are unchanged from predecessor v6;
proofs/root only changed. The complete frozen transcript module is retained
with only the old cfg(kani) state constructor appended. The powers function
is exact frozen text inside a factored module. All nine release Verified
fields remain native; the other three frozen fields are prover-only cfg.
No production source or candidate adoption changed; no new source decision.

Source-only reconstruction v2 matches every input source hash. v1 omitted
three inactive inventoried warm-workspace files and was rejected before any
compiler; v2 copies their historical bytes and distinguishes them from the
Cargo explicit lib-path import graph. No binaries, GOTO objects or caches are
published. Tools/source/import/commands/pre-post identities are in the two
attempt input/receipt files and the packet manifest; check.py is read-only.

## Validation

Only the smallest new target compiled, then verified in the pinned warm
Kani0.67.0/rustc1.93.0-nightly53732d5e0 native arm64 environment. Source revision
26990758ee; exact optimized flags/tools/target pinned in input.json. Default
checks with unwinding assertions, no uninit-checks or custom trusted axioms.
No unchanged full replay, NUC or SBF operation.

- v1 compilation exit0, wall1.1342819165s, peak RSS439058432B, aggregate sampled
  RSS462241792B, swap0.
- v2 verification exit0, wall70.4287455827s, peak RSS2989588480B, aggregate sampled
  RSS4141776896B, swap0; 0/2105 failed, 3/3 covers satisfied.
- Both used one atomic shared compiler lock, 4GiB sampled aggregate watchdog,
  180s wall guard. Neither guard fired. No #print axioms: Kani only, no new
  Lean theorem or axiom.

The next enclosing connection still requires actual SDK/native installation and
coherent caller/oracle/source transport, owned jointly with the lead's import
work; S2 remains transferred. Those premises remain explicitly open, rather
than being replaced by this control harness.
