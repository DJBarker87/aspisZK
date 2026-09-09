# Fixed C1 leaves a three-helper curve, not a quadratic claim error

Research base: `1b8f72d9de123b16eb831754e58518e66a33d3f3`.
This is scoped mathematical research; no production, proof grammar, query,
field, domain, transcript or 40,282-byte body changes.

## Exact reduction and its boundary

`FixedC1HelperReduction.lean` connects the literal selected 26+3 scalar-power
batch to a three-lane received-word curve. Its replay status is recorded
below; no general far-acceptance bound follows from this algebra alone.

Let `p` be the fixed 26-component C1 message, and let the three received C2
words be arbitrary, potentially non-polynomial. With the actual source
column order, write

```
C(gamma) = sum_{j=0}^{25} gamma^j p_j
h(gamma) = H + gamma G + gamma^2 D.
```

For exact C1, the selected received batch is exactly
`encode(C(gamma)) + gamma^26 h(gamma)`. For nonzero gamma and any original-code
message U, define

```
U_normalized = gamma^-26 * (U-C(gamma)).
```

The original received batch agrees with `encode(U)` at a stored symbol if
and only if `h(gamma)` agrees there with `encode(U_normalized)`. This
preserves each actual four-slot fibre, not merely an average agreement rate.
The normalization maps message coefficients to message coefficients, so it
does not assume helper code membership or choose a decoder candidate.

There is also a local version: if actual C1 agrees with p only on a fixed
support S, the same equivalence holds on S. Nothing is asserted about the
excluded C1 symbols. This matters because `earlyC1 = some p` implies a large
own support, not exact polynomiality of the entire received C1 word.

The exact-C1 version requires **all 26 lanes** to be codewords. Knowing only
the sixteen semantic lanes are exact leaves thirteen unknown received lanes,
not three. The local-support version provides the legitimate way to consume
the existing 26-lane early object's support.
These are the existing QM31-valued mathematical message/oracle types.
Canonical M31 C1 descent, authenticated access to the fixed received word,
and executable coefficient extraction remain separate obligations; this
identity does not manufacture any of them from a root.

## The C1 claim error does not disappear

For any linear functional ell (including each ordinary MLE row and each
proved natural-circle OOD functional), let

```
E_C1(gamma) = sum_{j=0}^{25} gamma^j (claimed_j-ell(p_j)).
C_helpers(gamma) = claimed_H + gamma claimed_G + gamma^2 claimed_D.
```

The literal full claim discrepancy is

```
E_C1(gamma) + gamma^26 * (C_helpers(gamma)-ell(U_normalized)).
```

After scaling by gamma^-26, the first summand is a **Laurent** polynomial
with powers from -26 through -1. It is not removed by knowing C1 or by
subtracting its genuine codeword. The unknown helper word has degree two;
the C1 claim-error polynomial can have degree 25, and a fixed full tuple's
complete scalar-power claim error still has degree at most 28. If the
normalized candidate is chosen after gamma, it cannot itself be treated as
a fixed degree-two polynomial.

The reduction therefore changes the dimension of the unknown **received
oracle** problem without awarding an unjustified two-root claim bound.

## Exact falsifier for the two-root shortcut

The control [fixed_c1_helper_control.py](experiments/fixed_c1_helper_control.py)
uses exact arithmetic in F31. All C1 and C2 received words are zero
codewords; the OOD answers and final polynomial are zero. Fix the row0 C1
claims to be the 26 coefficients of

`E(X)=product_{r=1}^{25}(X-r)`.

Those coefficients are fixed before gamma. With zero inactive and other
ordinary rows, the corrected shifted row discrepancy is `kappa*E(gamma)`.
It vanishes at exactly 25 nonzero gamma values, for every nonzero kappa.
At such a prefix the zero compact responses, zero final and zero query
residuals are compatible with the image-aware relation game. This is **not**
a claim that the earlier selected semantic/payment checks accept this
all-zero table and those claims.

The script checks all 900 gamma/kappa pairs: 750 have zero shifted prior.
It also exhausts all 29,791 quadratics and finds none that represent
`gamma^-26 E(gamma)` on every nonzero gamma. Thus the proposed two-root
claim bound is false even with exact C1 and exact helper codewords.
The same symbolic polynomial construction has 25 distinct nonzero roots in
QM31 because its characteristic exceeds 25. This is a lower-bound
obstruction to the shortcut, not a universal acceptance probability or
payment forgery. Other challenge collisions are not ruled out.
The saved output is [fixed-c1-helper-control.json](experiments/fixed-c1-helper-control.json).

## A proved broader support cover and its selected instantiation

`ThreeHelperCover.cover_dichotomy` now proves the following construction for
an arbitrary linear code and fixed finite support. `ThreeHelperSelected`
also instantiates it with the actual selected original-code encoder and
fixed-C1 normalization. Image/row probability composition remains separate;
this is not yet a completed acceptance game theorem.

Fix a support S where C1 equals its pre-gamma message p. Define Good from
the three-helper curve and the existence of an original-code candidate
missing at most C fibres of S. This definition depends on the fixed received
words and S, not on an actual later candidate or successful provider return.

- If fewer than three good gammas exist, charge at most two gamma values.
- Otherwise choose three distinct good gammas and corresponding codewords.
  Their common agreement support has size at least `|S|-3C`. Interpolate
  these three codewords in gamma. On the common support, the received
  quadratic curve equals that interpolant identically.
- Any other C-close candidate agrees with the interpolant on at least
  `|S|-4C` fibres. If `|S|-4C>256`, the proved original-code overlap cap
  forces them to be the same global codeword. Therefore one pre-gamma
  helper tuple covers every qualifying candidate, including adaptive
  candidate selection. Its C1 components are p by construction, rather than
  by moving a post-gamma tuple backward through the transcript.

This is a real dimension-dependent cover argument, not a radius sweep. For
an exact entire C1 support, the condition permits `C≤65471`. For the
existing early-C1 own support of size 245,609, it permits `C≤61338`.
Combining the latter with the previously proved four-fold geometric factor
and the two-pole allowance suggests the sufficient analysis threshold
`4*15334+2=61338`. The excluded C1 fibres remain excluded from this support
argument; they are not presumed code-consistent.

The literal `ThreeHelperSelected.early_cover` endpoint takes
`earlyC1 received = some p` and a fixed nonzero challenge set G. It obtains
S from that object's own support, deriving `|S|≥245609` rather than assuming
candidate membership. It then proves the dichotomy

```
fewer than 3 helper-good gammas in G
OR
exists h : Fin 3 -> original Message, fixed before gamma,
  for every gamma in G and every original message U,
  at most 61338 raw-batch mismatching fibres on S
    => U = C(gamma) + gamma^26 * sum_{j=0}^{2} gamma^j h_j.
```

The selected bridge proves the helper degree, uses the actual original-code
overlap cap on arbitrary S, transports the **same bad-fibre set** through
the affine normalization, and recovers coefficient-message equality using
the pinned encoder injectivity proof. The helper messages are chosen from
proved code-range witnesses, not supplied through a membership hypothesis.
The whole tuple exists mathematically before gamma; there is no claimed
efficient search or rewind algorithm for finding it.

These larger selected regions do **not** cover all far executions. They
do not give 100 bits from queries alone, eliminate the degree-28 claim
error, establish a bounded rewind extractor, or prove payment validity.
The none case of `earlyC1` is not asserted to satisfy this conditional
endpoint. A fewer-than-three Good branch contributes at most two gamma
values **only when the event actually requires reaching Good and the fresh
conditional law is justified**; it is not a bound on all accepted sparse
executions. The actual quotient/fold/image/row game composition must still
be carried out before claiming the broader probability endpoint suggested
by `4*15334+2=61338`.
No new numerical security level is assigned here.

The strict condition is necessary for this generic statement. The independent
[three-helper control](experiments/three_helper_cover_checks.py) constructs
four good F7 parameters at `|D|=4, B=1, delta=0` with no quadratic cover.
Adding a fifth coordinate enforces the strict margin; its exhaustive family
retains both dense and sparse Good outcomes. This is a generic code-model
regression, not a selected payment or adversarial-protocol experiment.

## Existing reduced strategy harness audit

`radius_strategy.rs` fixes an abstract two-fibre noise word and exhausts
compact responses plus affine final choices in its declared F11 game. It
does not enumerate arbitrary three-helper oracles. Its `value[alpha][prior]`
table uses the scalar prior as a state independent of the chosen final;
the final enters the query residuals. Transporting an actual running
relation to a different final also changes its discrepancy by the folded
weight pairing with that final. A new source-shaped strategy experiment
must include that coupling, not merely reuse the old scalar table as if it
were a complete actual relation-game optimizer. The old report's restricted
game evidence remains valid within its declared model.

## Proof/evidence status

The generic `ThreeHelperCover` replay is green: exit 0, 13.53 seconds,
5,638,488,064 bytes peak RSS, zero swaps; its three axiom audits use only
`propext`, `Classical.choice` and `Quot.sound`.
Source SHA256 `83554ad47bca052f4f44656f28402c4beaa0a555b1c6d909b200556259f463e7`;
olean `d8af96cfc12e2e5e35e7bee685c35d61bae59f311cc961d50df09075851303ea`.
See [three-helper-cover-v2.log](experiments/three-helper-cover-v2.log).
The failed v1 local coercion goals remain recorded.

The actual selected source-shaped specialization and early-support corollary
are green: exit 0, 15.98 seconds, 5,734,105,088 bytes peak RSS, zero swaps,
six standard-only audits. Source SHA256
`838f3a3930ab82c34578b4c852d2b47b6f0eb25a9dab1a6479150fda3ae31891`;
olean `42bc51f23059f9654011604cf0662644864e1401c0c55a31d76b93e8222d8c7c`.
See [three-helper-selected-v3.log](experiments/three-helper-selected-v3.log).
Failed v1/v2 concerned a missing evaluator unfold and an explicit classical
predicate instance, respectively; their source obligations are resolved in
v3 without changing the mathematical statement.

The exact selected affine leaf is also green: exit 0, 21.01 seconds,
5,738,283,008 bytes peak RSS, zero swaps, all twelve audits standard-only.
Source SHA256 `424204c75d0a9672310030a01557ca2ebcab3915064f11a5680067bad34a682e`;
olean `aca2f04d7a4751d0d13706fd90ec048f2e3082453feda13492706a8ce5e89ece`.
See [fixed-c1-helper-v8.log](experiments/fixed-c1-helper-v8.log).

Its earlier concrete sum specializations hit elaboration limits, not a
disproved mathematical statement. The generic scalar-power split and its
finite-enumeration transport both replayed successfully. The explicit-type
diagnostic identifies two sources of conversion work: the imported
SimplexCategory finite enumerations versus `Fin.fintype`, and direct
quadratic-tower additive instances versus their semiring projections.
The failed scoped conversion attempt increased only recursion depth, not
the 7-GiB memory cap, and still hit the existing heartbeat limit. The final
repair instead proves concatenation using **only an additive commutative
monoid**, passes the actual finite enumerations, then applies the local
high-block scalar factorization. No semiring-to-additive conversion remains
at the whole-sum interface. Final recursion depth is back to 200; no larger
memory or heartbeat cap was used. Failed logs v1-v7 remain historical
evidence, not claimed results; no `sorryAx` appears in the final audits.

The exact affine proof reuses pinned V7 encoder linearity and
the unchanged actual raw-batch definition. The runner checks
the complete imported research closure against the stated base and the
borrowed formal closure against `26a9cd4718aae9f9de7ef1c3394fb74a229085d5`.
No theorem depending on a failed replay is reported as established.

Reproduction commands (choose a fresh log filename):

```sh
bash docs/research/v8-no-work-100-20260907/experiments/run_fixed_c1_helper.sh /tmp/fixed-c1-helper-recheck.log
bash docs/research/v8-no-work-100-20260907/experiments/run_three_helper_cover.sh /tmp/three-helper-cover-recheck.log
bash docs/research/v8-no-work-100-20260907/experiments/run_three_helper_selected.sh /tmp/three-helper-selected-recheck.log
python3 docs/research/v8-no-work-100-20260907/experiments/fixed_c1_helper_control.py
```

## Decision and next obligation

This continuation constructs a selected helper-message cover in a broader
fixed-C1 regime without changing any verifier check or paying a target-family
union. It also rules out reducing wrong-C1 claim cancellation to degree two.
The decisive next composition is the actual quotient/fold-to-original
message bridge and carried image/row game on this enlarged covered region,
with the same fixed helper tuple and a full degree-28 claim discrepancy.
The remaining accepted outside-region/early-none mass must stay explicit.
Neither this theorem nor its generic control licenses a global security
certificate, FS lift, full-view simulator, CU claim, or payment extractor.
