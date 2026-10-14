# One sampler schedule for the 33 R1 challenges

The new sampler definition connects the previously checked local hash edges
and query sampler in their intended order. It reuses the old generic sampler,
oracle-program evaluation, background-answer laws and q22 scan. This is a
model integration step; it does not instantiate the complete Fiat–Shamir
security theorem or prove correspondence with Rust execution.

## Schedule and reuse

`UnifiedSampler.Public` contains public bytes, their address-size bound and
the variant tag. C1 remains the first prover message. The initialization
hash therefore binds a prover-selected commitment; C1 is not hidden in a
fixed public parameter or an oracle-dependent initial state.

| Row | Sampler operation | Checked connection |
|---|---|---|
| 0 | Hash public bytes and C1, absorb the fixed empty record, squeeze and advance | `DuplexSamplers.initial`, `PublicInitFrame`, `RowZeroCodec` |
| 1–25 | Absorb payload, squeeze and advance | `DuplexSamplers.plain` |
| 26 | Absorb payload, squeeze and advance, then hash the opening-domain frame | `DuplexSamplers.reseeded`, `OpeningReseedFrame` |
| 27–30 | Absorb payload, squeeze and advance | `DuplexSamplers.plain` |
| 31 | Absorb payload, read all eight squeeze/advance pairs, run the existing stopped q22 scan | `QuerySampler`, `QuerySamplerBridge` |
| 32 | Absorb the next payload using q22's selected continuation, then squeeze and advance | `UnifiedContinuation` |

The generic `QuerySampler.chain` output and read-set lemmas use induction on
the number of pairs. The eight-pair bridge applies those symbolic lemmas;
it does not reduce a large concrete sampler tree. Its output equals the
existing `QueryFirstRead.result`, including failure and the selected state.
All eight pairs are read even when the scan selects an earlier continuation.

`UnifiedContinuation.query_then_rho_firstCell` proves that row 32 starts
with an absorb frame containing that selected state. It does not substitute
the eighth advance state or assume the selected index. This equality holds
for any oracle, without a collision exclusion.

For valid non-query rows, `UnifiedSampler.unified_law` reuses the local
ordinary/initial/reseeded laws to obtain exactly the mean over a fresh
squeeze answer and fresh carried state. This is the independent-answer law
used by the framework, not an assertion that an adversary's shared-oracle
answers are independent. The previously checked completion and first-read
arguments still have to connect the complete protocol to this law.

`RowZeroCodec` connects the fixed row-zero address to the ordinary codec
under explicit premises that label zero is 160 and the selected payload
encodes the five-byte empty record. Its decode and indexed-read conclusions
reuse `Params.decEnc` and `IndexedMessage.read_encoded`. Concrete source
codec instantiation remains open.

## Scope and remaining obligations

`roundCount` is 33; the sampler is total for arbitrary natural indices and
message constructors. A wrong constructor uses a separately documented
dummy-query branch. `messageValid` describes the permitted constructors,
and the independent-answer theorem requires it. No acceptance claim is made
for malformed messages: a future decision/classifier must reject them and
enforce the 33-row schedule. `firstCell_some` also covers totalization; that
fact alone is not a validity or security result.

The definition leaves payload codecs, challenge maps and public-byte
encoding abstract. It does not discharge field sampling, canonical Rust
parsing, public/account authentication, settlement or source refinement.
The structured completing decoder must still be lifted to this exact
prefix/message/challenge representation for every round. D1/D2/D3,
injection and density must then be composed for the complete instance.

The eventual global bound retains its adversarial oracle-query factor and
collision terms. A local coefficient near `2^-105` is not an absolute
`2^-100` bound for arbitrary oracle-query budgets. No work-normalization or
grinding credit is introduced. Universal mask rank and the full privacy
simulator also remain open.

Focused NUC evidence, exact failed and final sources, resource receipts and
the final combined axiom audit are retained in
[`evidence/lean-unified-sampler-20261014/`](evidence/lean-unified-sampler-20261014/).
All eight final targets passed. The combined checkpoint took 1.49 s, used
3,521,724 KiB peak RSS with zero swap, and reported 24 standard-only axiom
audits. Each attempt ran in its own 4G/6G/0 high/max/swap scope.
No Rust source or runtime artifact changes in this step.
