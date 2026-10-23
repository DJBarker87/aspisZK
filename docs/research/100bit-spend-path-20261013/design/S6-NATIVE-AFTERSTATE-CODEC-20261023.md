# S6 complete native 688-byte afterstate codec — 2026-10-23

## Enclosing obligations closed

`S6NativeAfterstateCodecV1.lean`, namespace `AspisS6NativeAfterstateCodec`, proves
all of the following on the original full
`AspisR1TerminalDecoder.pool_v1.pair_terminal.PoolV1PairVerifiedAfterstateV1`:

```lean
-- TOTAL: arbitrary slices, including every rejection path.
∀ bytes : Slice U8, ∃ result,
  decode_pool_v1_pair_verified_afterstate_v1 bytes = ok result

-- TOTAL: arbitrary full native records, including validator errors.
∀ afterstate, ∃ result,
  encode_pool_v1_pair_verified_afterstate_v1 afterstate = ok result

-- ACCEPTED-ONLY inverse: actual decode is the sole premise.
∀ (bytes : Slice U8) afterstate,
  decode_pool_v1_pair_verified_afterstate_v1 bytes = ok (RustOk afterstate) →
  ∃ encoded : Array U8 688#usize,
    encoded.val = bytes.val ∧
    encode_pool_v1_pair_verified_afterstate_v1 afterstate = ok (RustOk encoded)
```

Every decoder/encoder in these statements is the original extracted native
function in `AspisR1TerminalDecoder.pool_v1.pair_terminal`. No reference decoder,
record association, encoder-success, child-success, canonicality, validation,
fixed-length or byte-correspondence premise remains. The public theorem
`accepted_roundtrip` also provides the weaker two-success form directly on those
same native functions, for enclosing codec composition.

The before/after statements are deliberately explicit. The preceding packet
proved `decode_reference bytes = RustOk a` plus
`encode_native (native a) = RustOk encoded` implies byte equality. The new theorem
uses the actual native decoder and its full returned native record directly,
and derives encoder success. This is a concrete implementation result, not merely
repacking the previous hypotheses. Quantification still covers every byte slice
and every full native record. All next-index, root and twenty frontier fields
are retained; no carrier is simplified.

## Proof connection

- Full Result equality connects five Lean-only decoder continuations to the
  complete original native decoder, including failure/divergence and every Rust
  error. The same generator checks textual re-expansion. No Rust body is changed.
- Full Result equalities for the actual native M31 byte helpers reuse the checked
  field inverse. The native standard Option operation is definitionally equal to
  the already extracted operation; its equality has no axioms.
- The actual complete native 32-byte digest decoder is TOTAL and its accepted
  inverse uses the actual native digest encoder. The original S2K encoder loop
  proof and checked byte expansion are reused.
- Native canonicality (eight-word loop) and afterstate validation (twenty-frontier
  loop) are TOTAL by remaining-count induction on the actual original loop
  bodies. Arbitrary noncanonical data returns ordinary Rust errors; it is not
  assumed away. These establish the reached integer/index bounds as part of
  totality, without a separate accepted-only overflow premise.
- The native decoder's actual reads, branches, exact-array conversions and map_err
  closures derive the complete header, index, root and ordered frontier frames.
  Its actual validator success follows from the same successful execution.
- S2K's original native `encode_exact` and rejection theorem now provide both
  encoder totality and success from that derived validation. Symbolic frame
  recomposition identifies all 688 bytes, including the header and success code.

A reference encoder is used internally as a byte-frame notation in shared lemmas.
Its equality to the actual native digest encoder is proved for **all** raw
inputs by `S6NativeDigestEncodeSourceEqV1.encode_eq`; it is not an implementation
association premise. Neither a reference decoder nor a substitute account or
statement carrier occurs in the final codec statements.

## Source freeze and trust boundary

The existing extraction manifest pins Rust revision
`0626294e34632812accf4cb14704f027368ea871`. The five relevant Rust files
(atomic statement, pair terminal, pair-tree profile, format and core field)
were checked byte-equal at that revision, the historical source freeze
`25866ec331cc7ce27dd9956609c11d32fa8fa58a`, and observed research
`fb849d31b5e731bb2d7dacdeb88e8bfc9cea7460`.
`s6-native-afterstate-codec-source-pins.json` records their exact hashes, the
existing Lean source hashes, and original extraction/type-adapter manifest
hashes. The prior byte-law packet already recompiles S2K's unchanged proof
sources against the selected local dependencies.

This reuses the existing Aeneas extraction trust boundary; it adds no per-call
association or custom axiom. The original source already contains the fixed-slice
helper used by that extraction, and the relevant file is byte-equal across the
three revisions. No production Rust, release verifier or wire format changed.
The codec functions are pure Result semantics. Current SDK/account borrowing,
allocation/abort observations, caller/error mapping and release binaries still
need their separate ports; these results do not manufacture those effects.

## Validation

Fifteen changed focused targets compiled in dependency order using the atomic
local lock, Lean 4.32.0, `-j1 -M4400` and warm dependencies. All selected targets
exited 0 with zero swap. There are 31 standard-or-empty axioms reports, containing
only `propext`, `Classical.choice`, and `Quot.sound`. Maximum selected peak RSS
was 3350740992 bytes; summed selected wall time was 237.142 seconds.
The final enclosing codec target took 5.954 seconds at 3295494144 bytes RSS, zero swap;
its seven requested axioms audits passed.

Exact target/source/revision/tool/import pins, commands, status, wall/RSS/swap
and audits are in each attempt selected by `s6-native-afterstate-codec-targets.json`.
The full selected object hash closure is
`s6-native-afterstate-codec-import-pins.json`; no binaries are distributed.
The initial final-continuation proof needed the shared frame definitions unfolded
through transparent aliases; that failed attempt remains excluded, with no
installed `sorryAx` evidence and no resource ceiling increase. No unchanged full
replay, cold dependency build, heavy NUC job or SBF build ran.

Audit commands (source/evidence only):

```
python3 tools/s6-full-forest-roundtrip-20261023/factor-afterstate-decoder.py --native --check
python3 tools/s6-full-forest-roundtrip-20261023/factor-afterstate-decoder.py --check
python3 tools/s6-full-forest-roundtrip-20261023/check-native-afterstate-codec.py
```

## Remaining enclosing work

The complete native afterstate688 byte law and its internal arithmetic/totality
obligations are closed in the extracted semantics. Snapshot800, transition1520,
the complete forest1880 codec (both payment variants), and concrete installation
at the current owned adapter's source/caller ports remain. The full public
serializer, first-decoded semantic/public reuse, SDK state/effects/error/abort
and ordered-read transport are not closed. S1's original preparation/gamma and
resumed-powers caller ports remain. S2 is externally owned. The overall
≤2^-100 per-attempt soundness target is not yet established.
