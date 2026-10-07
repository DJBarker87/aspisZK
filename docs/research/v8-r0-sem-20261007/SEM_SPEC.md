# R0 semantic phase: draft for the lead, before proof

Date: 2026-10-07. Inspection revision:
`c4ca596c83e29e858e0ee88887ccf9f9ea987f5a`, branch
`research/v8-wide-reference-20261005`. **No protocol choice is approved here.**
The purpose is to replace the phrase “as in the V8 baseline before R17” by
reviewable alternatives and a precise statement shape. No soundness theorem
is proved. All unresolved definitions and required proof inputs are numbered
in the questions at the end; the Lean file supplies no instance of them.

The R0 document does not identify one complete semantic protocol. Its step 2
points to a baseline; its source-status item 6 names the positive-transfer
adapter; its opening statement accepts arbitrary points and `semantic : Prop`.
Consequently, giving an unconditional concrete R0 semantic definition now
would silently make the decisions this task reserves for the lead. The draft
below transcribes the retained source, exposes the alternatives, and states
what a selected version must establish. [R0], [B1], [Opening]

## Source pins and scope

Every source link below means its contents at the inspection revision above,
not a moving main branch. LOG.md records last-change revisions and SHA-256s
for the main source files. The historical baseline note is pinned to
`4c91f97ac6576201f90d41c2a575e54c026e3796`; the positive-profile report names
`33e13de4e4b8bfdef7f3f2fb2e472b34db44865e`; the positive degree report names
`d5507a8f247bbed7cd35591c240d8d7a40af67a0`. They describe different stages,
not one interchangeable deployed artifact. [Baseline], [Positive], [Degree]

The maintained `v8-no-work-100-20260907/experiments/performance_verifier.rs`
is the full semantic driver found here. The copied
`v8-positive-complete-devnet-20260909/upstream/performance_verifier.rs`
retains the same semantic structure. In contrast, `relation_callback.rs`
explicitly treats its semantic prefix as opaque and cannot specify SEM.
No unique “before R17” commit/feature set is stated in R0. Q1 must select it.
[Driver], [Snapshot], [Callback]

Read the literal scalar functions in [Terminal] together with its generated
copy tables [CopyConstants]. Feature-gated factor/selector optimizations do
not by themselves identify the mathematical relation. The promoted V8 Lean
models [Wire], [MaskDegree], [PositiveDegree], [CopyDegree] explicitly leave
source-operation correspondence as a boundary. They are useful inputs, not
an existing R0 semantic soundness theorem.

## A. Round-by-round source transcription

Let F = ZMod(2^31-1), K = QM31 (size p^4), and E = WideExact (size p^8).
The entire semantic phase below uses K. E first appears in R0 step 4, after
the semantic and circle phases. The 29 opening messages represent 26
F-valued C1 lanes and three K-valued C2 lanes. Source names are: C1 lanes
0–15 physical semantic columns, 16–25 mask-only columns; C2 lanes 26=H1
(copy helper), 27=G (mask), 28=D (opening/hiding lane). D is among the 87
claims but excluded from the semantic terminal's 84-claim projection.
[R0: §2][R0], [Baseline: selected source][Baseline], [Terminal:28–68,1185–1309][Terminal]

In this table, “sample K” means the **retained bounded** `challenge_qm31`:
four sequential canonical 31-bit limbs, eight attempts per limb, fresh
squeeze/advance blocks as needed, failure rejects. “sample K*” means at most
three nonzero wrapper attempts, with any underlying failure rejecting. Under
independent answers the successful per-value mass for K is
`((1-2^(-248))/p)^4`, not a renormalized total uniform law. The proposed ideal
IOP can instead use uniform K/K*; choosing and connecting these two laws is
Q7. No 32-byte E reduce-mod rule belongs in this phase. [Sampler:360–435][Sampler],
[FieldMass:31–60][FieldMass]

| Order | Prover message / fixed input | Verifier action, checks and resulting data | Source |
|---|---|---|---|
| 0 | Public payment statement, live snapshot/candidate transition, profile/variant descriptor; C1 root for 26 words | Bind profile `AV8/payment-extraction/v1`, statement binding and C1. The positive variant additionally binds its canonical descriptor before C1. Canonical parsing and outer account/context checks are distinct; their exact inclusion is Q1/Q2/Q10. | [Driver:33–40,95–120][Driver], [PositiveAdapter:28–41][PositiveAdapter], [Callback:85–92][Callback] |
| 1 | None | Sample lambda in K. C1 is fixed first. | [Driver:38][Driver], [Sampler] |
| 2 | None | Sample chi in K. C2 is not fixed until after both values. | [Driver:38–39][Driver] |
| 3 | C2 root for H1,G,D, possibly depending on lambda/chi | Absorb second root. Bind the literal constraint-registry bytes and a 16-byte zero helper-sum record. The zero record is a claimed target; hashing zero does not establish a zero helper sum. | [Driver:39–40][Driver], [Zerocheck:80–107][Zerocheck] |
| 4 | None | Sample theta in K. | [Zerocheck:96][Zerocheck] |
| 5–14 | None between coordinates | Sample ten zerocheck coordinates a_0,…,a_9 in K, in order. | [Zerocheck:97–101][Zerocheck] |
| 15 | None | Sample mu in K, including zero. | [Zerocheck:102][Zerocheck] |
| 16 | Initial masked sum claim C in K; allowed to depend on all prior answers | Absorb `(degree=27, rounds=10, C)` under the initial-mask-claim label; sample eta in K*. The source performs no separate authentication that C equals the Boolean sum of the committed mask. Q6 must account for this. | [Hiding:375–389][Hiding], [Driver:41–42][Driver] |
| 17+i, i=0,…,9 | 27 K values: coefficient 0 and coefficients 2,…,27 of p_i | Set coefficient 1 to `c_i-2*p_i[0]-sum(p_i[2..27])`; absorb round byte i and the 27 values; sample r_i in K; update `c_(i+1)=p_i(r_i)`. Thus p_i(0)+p_i(1)=c_i by the construction. The honest polynomial's degree is a separate obligation. | [Driver:43–55][Driver], [Producer:93–116][Producer], [Wire:13–72][Wire] |
| 27 | 87 canonical K values `v[j,l]`, three rows of 29 | Compute the three source points from r as below. Feed only lanes 0–27 of each row into the terminal. Check terminal equals c_10; public validation failures reject. All 87 values are subsequently absorbed as one record before z0. Terminal evaluation is deterministic, so its placement before that absorb does not change the challenge order. | [Driver:57–62,78–91][Driver], [Inactive:49–54][Inactive], [Points:529–545][Points] |
| Handoff | No further semantic challenge | Output the three points, all 87 claims and the fixed inactive set I. This supplies only three fields of `Opening.Data`; W is already fixed, and z0,z1,y arrive in step 3. Coordinate/basis transport is Q4. | [Opening:Data,eqWeight][Opening], [Inactive:90–108][Inactive], [R0:§2 steps 2–3][R0] |
| Boundary after SEM | Receive y0 only after z0, then y1 only after a distinct z1 | Use the retained secure-circle/retry policy and reject exhaustion, if Q12 approves it. This is outside epsilon_SEM. The source success conditions are stronger than non-rationality. | [Inactive:51–60][Inactive], [CircleSource], [CircleRows] |

The labels in the order column count message/check stages; there are exactly
**25 field challenges**: lambda, chi, theta, ten a coordinates, mu, eta, and
ten r coordinates. There are ten adaptive sumcheck rounds, not one atomic
SEM draw. A sum of semantic error contributions is not automatically a
D2 bound for a single synthetic “SEM round”. [Driver], [Zerocheck], [Hiding]

### Points, claims, inactive set and mask convention

The source uses big-endian row bits. For r in K^10 define
`carry_i = product_(j>i) r_j`,
`succ(r)_i = r_i + carry_i - 2*r_i*carry_i` and
`xor12(r)_i = 1-r_i` for i=6 or 7, otherwise r_i. The source points are
`[r, succ(r), xor12(r)]`, not three independent random points. The source
claim is `v[j,l] = sum_(b<1024) t_l[b] product_i
(if bit_(9-i)(b) then P_j[i] else 1-P_j[i])`.
[Points:529–545][Points], [Producer:26–27][Producer], [V7Points:94–114][V7Points]

R0's `eqWeight` uses bit_i(b). If t uses the same row order, reversing the
point coordinates supplies the matching formula. If R16 basis transport
also changes the message coordinates, that reversal alone is insufficient.
`reversedSourcePoints` in Lean is an **unselected candidate**, with no
compatibility result asserted. Arbitrary R0.points cannot simply be identified
with the V7 source points. [Opening:eqWeight][Opening], [R0:§2 Codes][R0], Q4

The exact proposed I is
`{b<1024 | ACTIVE_ROW_MASKS[b/16] & (1 << (b%16)) = 0}` from
`pair_forest_copy_terminal_constants.rs`, or equivalently the compiled
inactive group/mask lookup used by the source. Inspection of the 64 literal
masks gives 214 active and 810 inactive rows. This is a deterministic
transcription count, not a new Lean proof. It differs from the older generic
state-only count 854. The later scalar v in R0 step 5 is a claim about the
batch on I; it is not an additional semantic message. [CopyConstants:5][CopyConstants],
[Copy:43–57][Copy], [Inactive:90–108,134–143][Inactive], [R0:§2 step 5][R0]

“Plain G” needs a precise meaning. The retained baseline terminal has

`M(z) = sum_(l<26) beta_l L0(z)^e_l t_l(z)
       + (1+L16(z)^26) G(z)`,

where `L0=sum_i(3+22*i)z_i`, `L16=sum_i(275+150*i)z_i`, beta_l is the
source tower rotation, e_0..15 are
`[0,2,4,6,8,10,12,14,16,18,20,22,24,26,13,25]`, and e_16..25 are
`[1,3,5,7,9,11,15,17,19,21]`. G is an ordinary committed 1024-cell lane,
but its terminal multiplier is not 1. The promoted `selectedMaskWrapperModel`
subtracts that weighted G and adds G; it is a different explicit formula.
“Not sparse-coded G” does not choose between these formulas. Q1/Q6 remain
open; the draft's `maskAt` has no instance. [Hiding:393–400,485–513,634–674][Hiding],
[MaskDegree:selectedMaskModel,selectedMaskWrapperModel][MaskDegree]

## B. Algebraic relation and extractor

This is the precise **candidate source relation**, with named source
operations whose Lean port is still required. It is not an assertion that
the opaque R0 semantic Prop already means this relation.

Let A_l(b) be the physical row table recovered from the message of t_l by
the selected inverse basis/row transport. Lanes l<26 must be F-valued; H1,
G,D are K-valued. Define each off-domain read by the big-endian MLE of the
same A_l, at the same three point maps. Do not reconstruct a trace from
independent favorable point values. [R0:§3 F7,§5 field descent][R0],
[Producer:26–45][Producer], [Recover:43–69][Recover], Q4/Q11

### Unrandomized constraints

The candidate must satisfy every selector-weighted source equation below at
all 1024 Boolean rows. The **literal operations and selectors in the cited
functions** define the catalogue; a future port must preserve them, including
slot reuse on disjoint row supports. Calling a callback `validPayment` is
not a substitute for these equations. [Terminal]

| Family / source slots | Exact algebraic requirement | Source |
|---|---|---|
| Four packed Poseidon lanes | Each evaluated two-round Poseidon residual is zero, with the exact external/internal selectors and round constants; unpack all base residual components on Boolean rows. | [Terminal:1243–1244][Terminal], `crates/aspis-statement/src/state_only_poseidon.rs::evaluate_state_only_poseidon_oracle_projected` |
| Scalar slots 0–15 | `semantic_initial_and_absorption(...).initial = 0`: selected state words equal prescribed zero/domain/length values on the literal first-node and rate-initialization selectors. | [Terminal:241–314,382–391][Terminal] |
| Scalar slots 16–31 | The literal absorption residual vector is zero, preserving `absorption_lanes_literal` selectors and constants. | [Terminal:316–362,382–391][Terminal] |
| Scalar slots 32–48 | With the path selector q: `q*b*(b-1)=0`, `q*(1-b)*(succ[k]-current[1+k])=0` and `q*b*(succ[8+k]-current[1+k])=0`, k<8. | [Terminal:394–428][Terminal] |
| Scalar slots 49–81 | On rows 1008,1010,1012: thirty bit equations `b*(b-1)=0`; current value equals the three 10-bit blocks weighted by 1,2^10,2^20; successor and xor12 padding-value coordinates are zero. | [Terminal:466–507][Terminal] |
| Scalar slots 82–83 | At row1014, `current[0]-current[1]-current[2]=0`; at the selected successor, `succ[0]-succ[1]=0`, with the exact selector. | [Terminal:510–518][Terminal] |
| Occupancy contributions, added to slots 0–11 | On the distinct occupancy selectors: o(o-1), a9*h-o, (1-o)h, (1-o)*digest[k], and the input/output occupancy equations all vanish. Output o is 1 for transfer, 0 for withdrawal. These contributions are ADDED to existing slots, not extra theta lanes. | [Terminal:530–579][Terminal] |
| Scalar slots 84–91 | The selector-weighted sum of digest differences is zero: anchor at row907, nullifier at427, recipient at475 (transfer), change at523, append empty/frontier nodes, candidate root and changed frontier at their exact selected rows. Preserve Merkle right-tweak and public append-bit branches. | [Terminal:609–695][Terminal] |
| Scalar slots 92–93 | Asset equality at rows44,508 and transfer row460; withdrawal public amount at row1010; variant-specific terms are exactly those summed by scalar_lanes. | [Terminal:1122–1183][Terminal] |
| Tagged copy relation | For every enabled link in the pinned 136-link registry, its producer and consumer tagged 16-tuples agree. Weights are 0/1 from variant and public append bits; tags, offsets, endpoint slots and repeated values must retain multiplicity. | [Copy:constants,235–261][Copy], [CopyOracle:106–166][CopyOracle], [CopyConstants:COPY_LINKS][CopyConstants] |
| Optional positive-transfer slot 94 | `A_1(1014)*A_1(1015)*A_3(1014)=1`. Its selected point expression is `v[0,1]*v[1,1]*v[0,3]-1`. It occupies slot2 of packed group23, already inside theta^27. It is absent in the baseline variant. | [PositiveAdapter:43–49,64–84][PositiveAdapter], [Positive:exact semantic change][Positive] |

The host `pair_forest_constraint_residuals.rs` is useful as an independent
catalogue, but its `all_zero` includes **zero padding of an unmasked trace**.
A masked C1 is not required to have all those free cells zero. Do not take
that host predicate unchanged as the accepted masked relation. Likewise,
recovery of positive amounts alone does not establish the owner key, note
hashes, paths, nullifier, public context or transition. Q2/Q3 must pin the
full intended witness relation. [Residuals:1–5,52–112][Residuals], [Recover], [Positive]

### Randomized terminal and helper equations

Let R_i(z), i<4, be the Poseidon packed values, S_g(z), g<24, the four-at-a-time
packing of scalar slots 0–93 (with zeros in unfilled slots), and C(z) the
copy residual. For the positive variant add the slot94 term before packing.
The retained composition and terminal are exactly

```
B_theta(z) = sum_(i<4) theta^i R_i(z)
           + sum_(g<24) theta^(g+4) S_g(z) + theta^28 C(z)
F(z) = eq(a,z) B_theta(z) + mu H1(z) + mu^2 (1-active(z)) H1(z)
T(z) = M(z) + eta F(z).
```

This is 29 theta lanes / degree28, and a quadratic mu check. It is not V7's
25-lane / degree24, linear-mu terminal. On Boolean rows the two helper
coefficients are `sum H1` and `sum_I H1`. Both must be separated in the
soundness argument; inactive H1 cells are not required to vanish pointwise.
[Terminal:1216–1309][Terminal], [Copy:1067–1071][Copy], [V5Residual:module introduction][V5Residual]

For clarity, the copy polynomial at a row with two producer and two consumer
slots is `active * (D_P*(H1*D_C+N_C)-D_C*N_P)`, where
`D_P=(chi-a0)(chi-a1)`, `N_P=w0*(chi-a1)+w1*(chi-a0)` and analogously for
consumers. Values a_s are `tag + sum_(j<16) lambda^(j+1)*tuple[j]` at the
specified source endpoints. Away from poles, local residual zero and the
two aggregate helper identities connect to the enabled-link LogUp balance.
That connection, tag injectivity, weighted multiplicities and collision caps
must be proved for this registry; they are not inherited just because it
has fewer links. [CopyOracle:128–178][CopyOracle], [Copy:235–261,334–357][Copy], Q5/Q13

**Initial claim:** the producer sends C before eta, but C is not checked
against sum M independently. Recommend counting the equation
`sum M + eta*sum F = C` when `sum F != 0`, a one-root eta event for each
candidate. This avoids assuming the absent `maskInitialExact` premise.
V7's `AcceptedMaskedBoundaryPieces` explicitly requires that premise; its
alternative theorem names the authentication failure. [V5Wire:474–548][V5Wire], Q6

### Relation and extraction target

For the lead's chosen public context x, define `R_pay(x,w)` by the exact
selected transfer or withdrawal validator, including which public/runtime
and spent-nullifier conditions belong to x. Define `Realizes(t,w)` by
literal extraction of witness fields from the transported physical C1 of t.
The desired deterministic result is: the unrandomized constraints, proper
field typing and public constraints imply `decode(x,t)=some w`,
`R_pay(x,w)` and `Realizes(t,w)`. This implication is a **proof target**,
not a premise that t already has a witness. [Recover:43–84][Recover], [Trace:52–72][Trace], Q2/Q3

The proposed full extractor reads commitment-bound words at root-fixing
times, enumerates the joint-close Lambda (threshold38230), transports and
descends each candidate, decodes its C1 and runs the selected validator;
it returns the first `(t,w)` passing the validator, or none. Transfer w
contains the input key/salt/value, pair leaf and selected side, 20-level
membership path/index, three super-root siblings/directions, and recipient
and change owner/salt/value. Withdrawal has input and change, plus its
public amount/destination context. The retained executable endpoint is
transfer-only and assumes it is given recovered canonical C1; it is not a
proof of extraction from an accepting transcript. Time bounds and the
hash-to-word connection are separate questions. [R0:§7.1][R0], [Recover:43–84][Recover],
[Trace:52–72][Trace], Q2/Q10/Q14

### Comparison with the V7 relation

| Item | V7 inventory's actual relation | Proposed source-shaped R0 draft | Required action |
|---|---|---|---|
| Public/witness objects | V5PublicStatement, coherent extracted V7 trace | Pair-forest transfer/withdrawal public objects plus live snapshot/candidate afterstate; optional strict-positive transfer | Define and prove a new relation/extractor bridge; not a renaming. |
| Terminal | 25 lanes, theta degree24; `eq*constraint + mu*helper` | 29 lanes, degree28; quadratic mu helper expression; optional packed positive residual | New terminal failure classifier and changed caps. |
| Mask initial sum | V7 boundary pieces require authenticated initial mask sum | Retained driver only absorbs C before eta | Prove an authentication route, or count the proposed eta event. |
| Point map | `[r,succ(r),xor12(r)]`, big-endian MLE | Source agrees, but fixed R0 input currently permits arbitrary points and uses little-endian eqWeight | Prove chosen transport; do not assume identity. |
| Claims | 87 coherent-extraction claims; terminal projects to84 | Same source shape; R0 dot-product/message convention differs | Exact evaluation/transport theorem. |
| Copy registry | 183 links; degree16 compression; pole366 + collision365 | 136 weighted pair-forest links; degree at most16 compression; actual active set214/1024 | Generalize generic arguments and instantiate actual registry. |
| List timing | C1 family fixed pre-lambda/chi; width29 family fixed post-C2/pre-theta | Same intended causal split, but R0 Lambda is over E and exact encoders | Typed embeddings and list/fixing proofs. |
| G / channel | Literal selected mask/hiding factors in the V7 semantic plan | “Plain G, one channel” is ambiguous about the mask factor; sparse/two-channel changes excluded by R0 | Lead must select literal mask function and descriptor. |
| 396430 | Whole causal K1.5 inventory, including 30 independent terms and 28 V7 opening roots | SEM-only causal experiment needs new theta/mu/eta accounting | Re-derive the row, keep any unused reserve visibly conservative. |
| Conclusion | V7 failure evidence/ideal subtotals under typed source bridges | R0 semantic acceptance and some candidate's exact claims, with no valid candidate | New event cover and probability composition. |

Sources for this table: [Inventory:37–118][Inventory], [V7Family], [V7Copy],
[V7Cover:576–632][V7Cover], [V7Closure:1–80][V7Closure], [V5Wire:474–548][V5Wire], [V7Points],
[Terminal], [Copy], [Opening], [B1].

## C. Draft soundness statement and budget

For a causal adversarial strategy A and the lead's selected sampler experiment,
let W(omega) be the commitment-bound words and Lambda(omega) their joint list.
Let `Exact(t,omega)` mean all 87 claims are the opening-layer dot products of
t at the transported three points. Let `Extends(x,t)` mean there is an actual
valid payment witness realized by t, not merely that the terminal accepts.
The recommended target is the **unconditional joint event**

```
Pr[ (forall t in Lambda(omega), not Extends(x,t))
    and SemanticAccept(omega)
    and (exists t in Lambda(omega), Exact(t,omega)) ] <= epsilon_SEM.
```

The requested implication form is also declared: if no candidate extends on
**every successful run**, then `Pr[SemanticAccept and exists exact t] <= epsilon_SEM`.
Fixing W after seeing lambda/chi and renormalizing on that C2 is a different
statement and loses the pre-C1 copy accounting. Q8 must settle the intended
quantification. Abort has probability weight and never accepts; no probability
is conditioned on sampler success. [R0:§7.2][R0], [V7Family], [V7Copy]

`lean/R0S/SemStatement.lean` defines Message, Phase, Challenge, causal Strategy,
compact polynomial/carry, both point conventions, explicit terminal assembly,
algebraic relation/extraction targets, Output and its adapter to the actual
R0.Opening.Data, and both SEM targets. SourceDraft and RelationDraft expose
unfixed functions; no instance exists. Experiment is over an **abstract**
finite type, with rational weights and optional successful coins. ProbabilityLaw,
KernelLaw, D2Target and CoverageTarget are unproved Props. Arbitrary record
values are not certified protocols or sampler laws. Instantiating K as QM31,
linking the kernel to the actual experiment and selecting the exact source
operations are mandatory, numbered tasks below.

Per-round bad sets are also Props: lambda roots of a nonzero characteristic
witness; chi poles or nonzero Wronskian roots; theta roots of a selected
nonzero row polynomial; the first nonzero-to-zero zerocheck slice; quadratic
mu cancellation; affine eta cancellation; and equal evaluations of distinct
sent/honest sumcheck polynomials. BadFamily must be constructed from the
**actual prefix**, unioned over the appropriate fixed list. The file does not
assume that arbitrary polynomials have the advertised degree or that every
failed witness hits them. Those are D2Target and CoverageTarget obligations.

### Proposed value, not a certified bound

Recommend initially retaining V7's conservative copy envelope and 30-root
reserve, correcting the source terminal degrees and charging eta:

| Challenge(s) | Proposed numerator | Fixing condition / proof still needed |
|---|---:|---|
| lambda | 100*2928 | C1 list fixed before lambda; actual registry compression argument |
| chi | 100*(366+365) | same C1 list, lambda fixed; poles counted before Wronskian roots |
| theta | 100*28 | post-C2 list fixed; 29 source lanes; packing faithfulness |
| ten zerocheck coordinates | 100*10 | nonzero Boolean constraint table; causal coordinate slicing |
| mu | 100*2 | quadratic aggregate in sum H1 and sum_I H1 |
| eta | 100*1 | C and candidate mask/real sums fixed before eta |
| ten sumcheck coordinates | 100*(10*27) | degree27 honest restrictions and causal sent messages |
| Conservative reserve | 30 | retained old allowance, not asserted new protocol rounds |
| Total | **397030** | all of the above remain proof obligations |

Thus `epsilonSEM proposedCaps = 397030/(p^4-1)`, approximately
**2^(-105.4011114998502643)**. Existing 396430/(p^4-1) is about
2^(-105.4032933796917766). The +600 is 100*(4 extra theta roots +1 extra
mu root +1 eta root); no extra factor100 is applied to the already list-scaled
copy subtotal. This derivation is a proposed envelope, not evidence that the
old V7 copy numbers bound this new registry. Q5/Q9/Q13 must validate it.

A tighter *candidate* envelope for 136 enabled-or-disabled slots is
100*(136*16 + (2*136)+(2*136-1)) + 100*(28+10+2+1+270) + 30
=303030, about105.790899 bits. This requires the weighted registry's tag,
characteristic-polynomial and no-pole arguments and is **not selected**.
Neither number is a final FS bound. A scalar source atom bound at most
1/(|K|-1) suffices for these proposed denominators; R0C's E sampler delta
is unrelated. Field sampler/ROM coupling remains Q7/Q10.

### Proposed proof route and estimated size

These are planning estimates in specialist working days, excluding lead
review and full runtime/Fiat–Shamir integration. They are not completion
promises. No part of this route has been started here.

| Work item | Existing material usable unchanged | New or relation-specific work | Rough size |
|---|---|---|---|
| Freeze typed wire, point map and Data adapter | R368 wire polynomial/boundary; V6 statementPoint formulas | Literal catalogue, coordinate/basis identity and selected mask convention | 200–500 Lean lines; 1–3 days |
| Honest semantic degree | R374/R376/R377, R381, R382, R384; PositiveResidualDegree degree14 addition; R386 copy model | Prove source-operator correspondence and combine actual masked terminal to degree27 | 400–900 lines; 2–4 days |
| theta/zerocheck/mu/eta classifier | Generic polynomial root counts; V5 adaptive degree27 and finite-family union machinery | 29-lane packing, quadratic helper separation, initial-claim eta event, causal coordinate slices | 350–800 lines; 2–4 days |
| Copy classifier | Generic Wronskian and characteristic-multiset lemmas in V7DeployedCopyLogUpCollisionBounds | Instantiate enabled tagged pair-forest links, weights, sums and root caps; V7 numeric wrappers do not transfer | 350–800 lines; 2–4 days |
| Lists and field transport | R0/Wide joint list cap100, subfield descent, exact encoders | Pre-C1 list, physical tables, post-C2 family and fixed-plan dependence | 200–500 lines; 1–3 days |
| Full algebra-to-witness implication | SelectedTransferPositive amount endpoint and related recovery lemmas are only partial; executable recovered_witness supplies a decoding recipe | Owner/note/path/public/transition correctness for every residual-zero candidate, masked/free cells, branch scope | 800–1800 lines; 4–8 days |
| Causal SEM probability/state cover | Generic finite probability unions and adaptive sumcheck roots; R601 successful field law | Actual Prefix/BadFamily, source/kernel coupling, nonzero eta retry law, D2 and event cover | 350–800 lines; 2–4 days |

Overall: roughly **15–30 specialist days, 3–6 thousand Lean lines** after the
choices are fixed; the extraction and source-catalogue boundaries dominate.
The algebraic lemmas can transfer by instantiation; V7's complete inventory,
terminal plan, accepted trace classifier and payment endpoint cannot be used
unchanged. CircleSource's successful non-rational/distinct results remain
available for a later step-3 state-function integration. A concrete retry-aware
FS decoder is outside this statement job and outside these estimates.

## D. Open questions for the lead

1. **Which source/profile is R0 step 2?** Select an exact revision, feature set, transfer/withdrawal scope and meaning of “plain G”. Recommendation: pin the cited pair-forest driver, choose the positive-transfer branch if strict positive outputs are required, and retain the ordinary 1024-cell G with its literal mask factor unless deliberately changed. Consequence: theta degree28 and ten degree27 rounds; a different G formula needs a fresh degree/source check. No variant is selected in Lean.
2. **What exactly is a valid payment witness and public context?** Does SEM cover transfer, withdrawal, live append transition, runtime binding and spent-nullifier freshness, or only the algebraic payment relation? Recommendation: name the exact validator and authoritative public inputs; keep externally authenticated account/freshness facts explicit. Consequence: a missing predicate cannot be assigned a numerical error; without positivity the old zero-output endpoint mismatch is not repaired by a larger small epsilon.
3. **Which unrandomized constraints are authoritative?** Approve the 94 source slots plus four Poseidon lanes, optional slot94, copy identities and public predicates above; decide masked/free-cell treatment. Recommendation: use selected terminal equations, not the unmasked host `all_zero` predicate; prove they imply the chosen validator. Consequence: no finite advertised SEM budget is justified without this deterministic implication. This fixes SourceDraft's residual/public operations and RelationDraft's witness predicates/decoder.
4. **What is the exact message-to-physical and point-coordinate transport?** R0 uses an R16-transported encoder and little-endian eqWeight; source MLEs are big-endian. Recommendation: freeze the inverse basis/row map and prove an evaluation identity, using reversed source points only if that is the resulting identity. Consequence: no new probabilistic loss for an exact equivalence; without it “87 true claims” is the wrong event. This fixes physical, openingPoints and realizes.
5. **Which copy registry and inactive set are intended?** Approve the 136-link pair-forest registry, variant/append-dependent 0/1 weights, tags, endpoint multiplicities and the literal 810-row complement. Recommendation: pin the generated arrays and prove agreement with the typed registry, helper equations and public append index. Consequence: old 2928/366/365 caps remain a proposal until re-established; the tighter 2176/272/271 alternative is not yet justified. This fixes copyAt, activeAt, inactive, enabledLink and both tuple projections.
6. **How are mask M, H1 sums and initial claim C handled?** Recommendation: retain the literal mask function and quadratic mu terminal; do not assume C=sum M or an honestly generated mask. Charge the affine eta cancellation event and prove the quadratic helper separation. Alternative: implement and prove an actual mask-sum authentication mechanism. Consequence: +100 mu and +100 eta roots relative to V7's bookkeeping; an independently authenticated C can remove the eta contribution. This fixes maskAt and the meaning of helper bad events.
7. **What probability experiment and sampler law does SEM use?** Ideal independent K/K* coins, or bounded source samplers with errors? Recommendation: state the ideal causal theorem plus a separately proved successful-subprobability source coupling; errors reject and are never renormalized. Consequence: the proposed 1/(|K|-1) envelope can remain if successful atom bounds hold at each prefix; otherwise use explicit per-round atom factors. ProbabilityLaw, KernelLaw and experiment coupling are unproved, not assumed instances.
8. **Where is the no-witness condition quantified?** Recommendation: the joint-event SEMTarget over the full causal run, with the stated implication corollary when no witness exists on every run. Do not condition on challenge-dependent C2/Lambda. Consequence: retains the C1-before-lambda copy argument; postselection could invalidate the claimed budget entirely.
9. **How do R0 candidates populate the two fixed families?** Recommendation: prove a pre-lambda C1 joint list of size100 and a post-C2/pre-theta full list of size100, with correct field/physical projections and terminal plans. Do not multiply them into10000 or select a new family per future challenge. Consequence: all candidate-dependent rows use the displayed factors100; a product-family requirement would materially worsen the bits and needs a new ledger.
10. **Which transcript/source/commitment facts are supplied to SEM?** Recommendation: first fix a causal word-commitment IOP (C1 before lambda/chi, C2 before theta, C before eta, each coefficient message before r_i, all claims before z0). Prove root-to-word and retry-aware source/ROM correspondence separately. Specify profile bytes, public binding and any retained nonce records; no grinding discount. Consequence: these obligations cannot be hidden inside the algebraic epsilon; FS collision/query factors are additional. This fixes legal prefixes, history and kernel-to-experiment coupling.
11. **Which typing and characteristic facts are available?** Recommendation: K is the exact QM31 tower, E the exact Wide extension, with explicit embedding and base-field typing of C1 obtained from canonical commitments/subfield descent; use the literal tower basis for packing. Prove tuple descent rather than assuming the selected candidate is typed. Consequence: zero added error if proved; faithful unpacking and small-characteristic Wronskian arguments fail without these facts. Generic K in Lean is not automatically asserted to have p^4 elements.
12. **What exactly crosses the SEM/step-3 boundary?** Recommendation: output only points/claims/I, then run the source secure-circle and distinct-second wrappers, reject failure and absorb y0 before z1. Keep z conditions outside SEM until their own state rows are integrated. Consequence: successful source outputs incur no rational/equal bad event; a full-uniform-circle alternative introduces roughly93-bit rows and changes the ledger. No circle assumption is silently bundled into SEM acceptance.
13. **Approve which provisional budget and bad-event partition?** Recommendation: start with the explicit 397030/(p^4-1) envelope, prove every cap and the prefix-local cover, and leave the 30-root reserve visible. The 303030 alternative needs the tighter copy argument. Consequence: proposed105.401111 bits versus old105.403293; neither is certified yet. If any nonzero-polynomial, degree, list-fixing or coverage obligation fails, report a finding instead of assuming it.
14. **What extractor and resource claim is required?** Recommendation: specify tuple-to-witness decoding plus the full chosen validator, returning an actual witness or failure; initially claim mathematical existence, then separately bound enumeration/decoding cost if knowledge soundness requires efficiency. The retained transfer executable starts from already recovered C1 and external context. Consequence: no extra algebraic error for a correct deterministic extractor; absence of a source-to-witness theorem or required efficient extractor leaves SEM/knowledge soundness open.

Questions 1–6, 8–11 and 13 determine the proof statement and must be fixed
before a proof job starts. Q7 must fix the probability semantics even if its
runtime coupling is scheduled later. Q12 can be deferred only by explicitly
keeping step3 outside SEM; Q14's existence/efficiency scope must be stated
before claiming knowledge soundness. No answer has been inferred from a
previous request to “continue”.

## Source references

[R0]: ../v8-wide-reference-20261005/R0_SOUNDNESS.md
[B1]: ../v8-r0-close-20261007/FS_LOG.md
[Opening]: ../v8-wide-reference-20261005/lean/R0/OpeningDefinitions.lean
[Baseline]: ../v8-no-work-100-20260907/baseline.md
[Driver]: ../v8-no-work-100-20260907/experiments/performance_verifier.rs
[Snapshot]: ../v8-positive-complete-devnet-20260909/upstream/performance_verifier.rs
[Callback]: ../v8-no-work-100-20260907/experiments/relation_callback.rs
[Producer]: ../v8-no-work-100-20260907/experiments/payment_extraction.rs
[Inactive]: ../v8-no-work-100-20260907/experiments/inactive_row_binding.rs
[PositiveAdapter]: ../v8-no-work-100-20260907/experiments/positive_transfer.rs
[Positive]: ../v8-no-work-100-20260907/positive-transfer-review.md
[Degree]: ../v8-no-work-100-20260907/positive-residual-degree-review.md
[Recover]: ../v8-no-work-100-20260907/experiments/recovered_witness.rs
[Sampler]: ../../../crates/aspis-core/src/transcript.rs
[Zerocheck]: ../../../crates/aspis-core/src/state_only_sumcheck.rs
[Hiding]: ../../../crates/aspis-core/src/state_only_hiding.rs
[Points]: ../../../crates/aspis-core/src/v6_transcript.rs
[Terminal]: ../../../crates/aspis-statement/src/pool_v1/pair_forest_semantic_terminal.rs
[Copy]: ../../../crates/aspis-statement/src/pool_v1/pair_forest_copy_terminal.rs
[CopyConstants]: ../../../crates/aspis-statement/src/pool_v1/pair_forest_copy_terminal_constants.rs
[CopyOracle]: ../../../crates/aspis-statement/src/pool_v1/pair_forest_semantic_oracle.rs
[Residuals]: ../../../crates/aspis-statement/src/pool_v1/pair_forest_constraint_residuals.rs
[Trace]: ../../../crates/aspis-statement/src/pool_v1/pair_forest_trace.rs
[Inventory]: ../../../AspisFormal/AspisFormal/Pool/V7K15FailureRootInventory.lean
[V7Family]: ../../../AspisFormal/AspisFormal/Pool/V7FixedTupleSemanticSecurity.lean
[V7Copy]: ../../../AspisFormal/AspisFormal/Pool/V7FixedC1CopyCollisionSecurity.lean
[V7Cover]: ../../../AspisFormal/AspisFormal/Pool/V7K15FixedFamilyCausalCover.lean
[V7Closure]: ../../../AspisFormal/AspisFormal/Pool/V7K15CausalProbabilityClosure.lean
[V7Points]: ../../../AspisFormal/AspisFormal/V6AcceptedPathObligations.lean
[V5Residual]: ../../../AspisFormal/AspisFormal/V5AcceptedTerminalResidualExtraction.lean
[V5Wire]: ../../../AspisFormal/AspisFormal/V5AcceptedSumcheckSourceBridge.lean
[Wire]: ../v8-full-view-zk-20260912/lean/AspisV8R19/R368WireSemanticCompatibility.lean
[MaskDegree]: ../v8-full-view-zk-20260912/lean/AspisV8R19/R382SelectedMaskDegree.lean
[PositiveDegree]: ../v8-full-view-zk-20260912/lean/AspisV8R19/R384PositiveDeltaDegree.lean
[CopyDegree]: ../v8-full-view-zk-20260912/lean/AspisV8R19/R386CopyDegree.lean
[FieldMass]: ../v8-full-view-zk-20260912/lean/AspisV8R19/R601ExactFieldMass.lean
[CircleSource]: ../v8-r0-close-20261007/lean/R0C/CircleSource.lean
[CircleRows]: ../v8-r0-close-20261007/lean/R0C/CircleRows.lean
