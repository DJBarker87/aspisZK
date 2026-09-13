# R13 shared-oracle transport evidence

Source pin: `769c732880e059f7e1c09df65333e5eeda20985a`.
This record is a source-facing finite-oracle boundary, not a
full-transcript privacy proof or publication authorization.

## Checked inputs

* `scripts/check_manifest.py`: 58 packet entries passed.
* `scripts/check_source_pins.py`: all 7 pinned source blobs passed.  The
  script expressly does not assert complete generated-q22 dependency closure.
* `python3 verify.py`: 51 tests passed, including the full-function
  transposition inverse, output-collision and address-alias cases, failed
  parses fixed pointwise, old/new prior-query hazards, cached histories,
  16-attempt decoding, and the leaf-salt-seed counting regression.
* `bash scripts/run_cpp.sh`: 2,916 complete finite worlds passed, checking
  both inverse identities and full-state marginals.

## Formal leaves

All of the following compiled one at a time with
`lake env lean -j1 -M1800` in the cached `AspisFormal` workspace, followed
by the `AspisV8R13.lean` aggregate:

* `OraclePartition`: split/reindex one oracle and retain fixed context.
* `SwapCells`: whole-function transposition and its reverse.
* `MovingLeaves`: `movingLeafEquiv` is an equivalence of
  `C × (Index → Key → Digest)` and
  `D × (Index → Key → Digest)`; its inverse rereads the same selected full
  answers and applies the corresponding inverse coin map.
* `FiniteOracleLaw`: exact uniform law from that equivalence, and the
  selected-answer-to-fixed-address law.  This repair adds the necessary
  decidable index equality for finite function enumeration and an explicit
  equivalence type; it does not change a theorem premise.
* `AdaptiveHistory`, `Disclosure`, and `MaskedFailure`: off-support
  public-history equality, disclosed-group preservation, and identity on
  failed parses.  The failure lemma repair only makes the otherwise
  uninferable failed-sum type explicit.

`#print axioms` reports only standard Lean axioms: `propext`,
`Classical.choice` where finite counting is used, and `Quot.sound`.
No `sorry`, new cryptographic assumption, or marginal-law premise was
introduced.

The focused replay used source revision `769c7328`, `-j1 -M1800`, and
reported zero swap throughout.  Wall time / peak RSS were:
`OraclePartition` 2.34 s / 816 MB, `SwapCells` 1.13 s / 815 MB,
`MovingLeaves` 1.14 s / 817 MB, `FiniteOracleLaw` 5.59 s / 1.329 GB,
`AdaptiveHistory` 1.31 s / 960 MB, `Disclosure` 1.07 s / 810 MB,
`MaskedFailure` 1.07 s / 831 MB, and the aggregate 1.55 s / 1.305 GB.

## Source adapters

`cargo test --offline --release -p aspis-prover --features
insecure-spend-fixture r13_real_ -- --nocapture` passed both tests.
They use a test-only child module of `state_only_hiding.rs`; production
visibility and protocol paths are unchanged.

1. The real private main builder, with the public 282-block fixture, preserves
   C1, all mask-only columns, H1 padding, and the mask nonce.  Its G hashes are
   `7f5ed7c7…f74778` before and `64cc15db…cae0a0` after; H1 remains
   `6afc7ac4…1d171d`.
2. The real domain-log-20 circle encoder and typed C2 leaf/parent APIs preserve
   eight selected full leaf answers and their diagnostic subtree root under
   full 32-byte input-cell swaps.

`scripts/build_evidence.py` additionally passed over the pinned main-word
codec: 282 expansion blocks and 11 diagnostic C2 pairs (304 oracle addresses)
change; the raw rejection skeleton, three-cut coefficient view, and complete
oracle inverse are retained.  This diagnostic uses 16 canonical table-row
leaves, not circle codewords or q22.

## Exact boundary and first remaining source proposition

The established boundary is the concrete whole-function moving-leaf
permutation, its finite uniform-law consequence, and source tests for the
actual main-mask bytes plus a real typed C2 encoder/leaf slice.  Main blocks,
C2 leaf inputs, and all remaining SHA inputs are still required to be
classified as a disjoint partition of one source random function; the
construction has not introduced independent hash oracles.

The first remaining proposition is: **for the actual prover chronology,
construct `phi_h` from the preserved complete C2 leaf answers/root and the
R12 fixed-complement/causal equations, and prove that it is exactly the source
callback transport at every selected three-cut read (with eta sampled after
the initial claim).**  Its proof must then supply
`publicRun_eq_off_support` with actual old-and-new C2 and main-expansion
support, including cached/prequeries and first-hit accounting for field
entropy, leaf-salt seed, derived main seed, and individual salts.  No q22
global bound, disclosure-opening equality, full public-only simulator,
later-transcript claim, retry/publication result, or full privacy claim is
made here.
