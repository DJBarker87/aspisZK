# R0 semantic soundness (premise SEM): proof job log

2026-10-08. Lead decisions Q1–Q14 as recorded in the job brief:
Q1 = positive-transfer branch; Q2 = algebraic payment relation **plus** live
append transition, runtime binding and spent-nullifier freshness, each
classified below as constrained by the proof or public-only.
Source: `crates/aspis-statement/src/pool_v1/pair_forest_semantic_terminal.rs`
and `docs/research/v8-no-work-100-20260907/experiments/positive_transfer.rs`
at branch revision `30793447d`.

## Q2 classification (from the source, before any port)

| Property | How the source treats it | Classification |
|---|---|---|
| Nullifier derivation | Computed digest bound to `public.nullifier` at row 26·16+11 (`public_digest_lanes`) | Constrained (Part C, digest family) |
| Membership root | Computed root bound to `public.anchor` at row 56·16+11 | Constrained: the path hashes to the *stated* anchor |
| Anchor is a genuine historical root | Not referenced by the terminal | **Public-only**: on-chain program check |
| Spent-nullifier freshness | Not referenced by the terminal; only the nullifier value is public | **Public-only**: on-chain program check against the spent set; not provable by this proof |
| Recipient and change commitments | Bound to `public.recipient` / `public.change` | Constrained |
| Append: new root and carry-level frontier | `after.next_root`, `after.next_frontier[carry]` bound in-circuit; snapshot frontier levels / empty roots bound as inputs | Constrained |
| Append: pool/domain match, sequence, capacity, unchanged frontier levels | `validate_transition`: a deterministic check on public data only | **Public-only**: decidable predicate on `x`; no proof needed, but the verifier/program must run it |
| Withdrawal amount range (`1 ≤ a < 2^30`) | Host check in `composition_parts` | **Public-only**: decidable predicate on `x` |
| Runtime binding (profile/variant descriptor, statement bytes) | Absorbed into the Fiat–Shamir transcript, not a relation constraint | **Transcript binding**: enters through the FS statement `x`, not `R_pay` |

## Findings so far

1. **Q1's branch is research-only.** `positive_transfer.rs`: "Opt-in research
   design change … No production feature enables this module." Choosing it
   for R0 means R0's semantic phase is not the deployed V8 semantic phase.
2. **Slot 94 gives field non-zeroness, not integer positivity.** Its residual
   is `A₁(1014)·A₁(1015)·A₃(1014) − 1`, which forces `A₁(1014), A₁(1015) ≠ 0`
   in F_p. Integer positivity additionally needs those cells to equal the
   30-bit range-checked values (`add_value_lanes`: bits on rows 1008/1010/1012,
   reconstruction into column 10). The link is through the copy relation and
   is a Part C obligation, not given.
3. **Conservation cannot wrap.** At row 1014, `A₀ = A₁ + A₂` in F_p. If all three
   are range-checked below 2^30, then `A₁ + A₂ ≤ 2^31 − 2 = p − 1`, so the field
   equation is the integer equation. This is an arithmetic fact; it still
   depends on finding 2's copy link.
4. **Freshness and anchor validity are outside any proof of this protocol.**
   Under Q2 they become explicit public predicates enforced by the on-chain
   program. The FS/SEM theorems hold *given* them; they do not establish them.

## Finding 2 resolved (positivity) — `R0P.positivity`

The copy registry (`COPY_LINKS`, tags 1124073486–1124073489, all weight kind
0 = enabled for every variant) links `(1008,10)→(1014,0)`, `(1010,10)→(1014,1)`,
`(1012,10)→(1015,1)` and `(1014,2)→(1015,0)`. With the value-row equations,
conservation and slot 94, `R0P.positivity` proves: input = recipient + change
**as integers**, all three below 2^30, recipient ≥ 1 and change ≥ 1. It uses
only `CharP K (2^31−1)`, so it holds in QM31 with no typing premise. Its
hypotheses are exactly what the G1 row lemmas and the copy-relation equalities
must deliver; the copy equalities themselves come from the LogUp argument,
which is probabilistic (λ/χ bad sets in the SEM ledger), not deterministic.

So Q1 delivers what was intended — **conditional on** copy-relation soundness
for these four links. Condition (i) is discharged: `positivity_of_families`
(`PositivityWired.lean`) derives the interface from G1's literal
`value_holds_iff` and `positive_holds_iff`. G1's finding 1 (two extra padding
equations) only strengthens the hypotheses and does not affect this proof.

## Compile record

| Target | SHA-256 | exit | wall | peak RSS KiB | swaps | axioms |
|---|---|---:|---:|---:|---:|---|
| `lean/R0P/Core.lean` | `eba6bb784803b5f00922724efc9997a8d5ab6bc55cd8c100bffd8a397dabe1f9` | 0 | 1.49 s | 3,327,872 | 0 | definitions only |
| `lean/R0P/Positivity.lean` | `0a7eaab784bc129b9995e3b7f18efde393e7d383686d1798bbe9fa7893a6ad1c` | 0 | 1.80 s | 3,327,496 | 0 | `positivity`: propext, Classical.choice, Quot.sound |
| `lean/R0P/PositivityWired.lean` | `9d601f1920c4700f2f08566cef66c9e43b5d3e9fceb9f9d9cc1ef4ce4471c7f2` | 0 | 0:01.79 | 3,328,412 | 0 | `positivity_of_families`: propext, Classical.choice, Quot.sound |

## G1

Value, Positive, Occupancy and Asset only. Inspection pin
`ebe7cbcdc315cde4f483f47a79262b8010984e98`; final Lean source revision
`9fd03f5c9e93f8c0e8cdd3d5b6fd9e38b2d810da`. Core.lean and other groups' sources
were not edited. Source T is `crates/aspis-statement/src/pool_v1/pair_forest_semantic_terminal.rs`;
source P is `docs/research/v8-no-work-100-20260907/experiments/positive_transfer.rs`.
All ports are over arbitrary `[Field K]`; no QM31 or characteristic premise.
The Family outputs are scalar residual contributions **before** tower packing,
as required by Core; no extraction or equivalence of assembled families is claimed.

### Literal ports and row statements

| File / family | Source ranges | Row-local result |
|---|---|---|
| Value / valueFamily | T:59,167–173,466–519; non-packed-range-audit branch 503–509 | Rows 1008,1010,1012: thirty Boolean cells, column-10 30-bit reconstruction, successor/xor12 column-10 padding zero. Row1014: `A0=A1+A2`; row 1015: `A0=A1`. |
| Positive / positiveFamily | P:10–12,64–70,78; T:28–34,1185–1191 for selected-claim layout | Exactly `A 1 1014 * A 1 1015 * A 3 1014 = 1`. `positive_claim_indices` derives indices 1,28+1,COL=3 from the three blocks of 28, and `positive_family_row_claims` connects this to Family. |
| Occupancy / occupancyFamily | T:60–61,521–578; literal non-semantic-factor-audit branch 539–545 | Common occupied/inverse/digest equations at rows 1017/1018, input `A10*(1-A0)=0`, output `A0=1` for transfer or `A0=0` for withdrawal. |
| Asset / assetFamily | T:59,1121–1141,1165–1181 | Asset equality at rows 44/508, additionally 460 for transfer; row 1010 column 10 equals the present withdrawal amount only in the withdrawal branch. |

Definitions retain operation order: reconstruct_10's nine reverse-fold steps
are written out without arithmetic simplification; range squares/subtractions,
the initial-zero selector sum, weighting loop, occupancy products/sums and
scalar Option-presence branch are literal. Only lemmas simplify equations.
The factored occupancy path T:580–605 and packed-range audit path T:510–511
are not selected. positiveSelector also transcribes P's ten ordered selector
multiply steps; the Family uses Core's Boolean-row selector interface.
No large constant tables occur in G1. The three-entry value-selector vector
is small; thirty bit lanes and eight digest lanes remain symbolically indexed.
Off support, the proofs use rowSel_ne; no 1024-row enumeration or concrete
Finset.univ is used. The only definitional numeral reductions are small indices,
casts and selector addresses, not State/Addr/field enumerations.

### Findings

1. **Requested G1(a), read as all range residuals, is false.** T:500–502
   includes range[31]=succ_z[10] and range[32]=xor12_z[10], in addition to
   the thirty bit equations and reconstruction. A trace zero everywhere
   except `A 10 1009 = 1` has all requested bits Boolean and all three
   requested reconstructions true, but range[31] at row 1008 equals 1.
   The failed shorter equivalence is not asserted. `value_range_zero_iff`
   and `value_holds_iff` prove the complete literal condition including both
   padding equations. Smallest correction to the requested statement: add
   those two zero equations at each selected value row, or explicitly restrict
   the equivalence to the first 31 residuals. No source/interface was changed.
2. **Positive source status:** P:1–4 states that no production feature enables
   this research adapter. It is ported because the lead explicitly chose it
   in Q1 and the G1 brief explicitly requests slot 94; it is not represented
   as the deployed V8 path. No positivity, copy-link or extraction premise is
   added by these ports.

### Build environment and final evidence

Host `dombarker@100.108.41.90`, workspace
`/home/dombarker/project-offloads/aspis-fs-generic-20261006` (B below).
Runner: `B/run.sh <attempt> R0P/<File>`; each file imports only R0P.Core,
which imports Mathlib.Tactic. Pinned Lean 4.32.0 with the captured lake environment;
`-j1 -M4500 -DElab.async=false`, MemoryHigh=5G, MemoryMax=7G,
MemorySwapMax=0, TasksMax=128, timeout 900 s. One G1 Lean job at a time, no cap
increase, no dependency/package replay. The final explicit reservation check
admitted 24 GiB populated + 7 GiB under the 55 GiB ceiling. run.sh itself has no
reservation-check code; its systemd scope enforces the stated memory limits.

LEAN_PATH starts with B/objects, followed by the captured environment's
`/home/dombarker/project-offloads/ZK-v7-one-tx-formal-consolidation-20260828/AspisFormal`
(C below): C/.lake/packages/{Cli,batteries,Qq,aesop,proofwidgets,importGraph,LeanSearchClient,plausible,mathlib}/.lake/build/lib/lean
(each member a separate path), C/.lake/build/lib/lean, then
`/home/dombarker/.elan/toolchains/leanprover--lean4---v4.32.0/lib/lean`.
Core SHA-256 matched locally and remotely:
`eba6bb784803b5f00922724efc9997a8d5ab6bc55cd8c100bffd8a397dabe1f9`.

| File | Attempt | SHA-256 | Exit | Wall s | Peak RSS KiB | Swaps | Axioms |
|---|---:|---|---:|---:|---:|---:|---|
| Value.lean | 711 | `90afff5dd9c8b70c6c183f6b3f2322d85d57fbcb548b530a98f69a91f1bccc12` | 0 | 2.43 | 3339316 | 0 | permitted subset below |
| Positive.lean | 713 | `7c318b973fcda478a003fb302d75eb75b6af318cca6d8e572ca66cd17dcfba3a` | 0 | 1.57 | 3318348 | 0 | permitted subset below |
| Occupancy.lean | 712 | `2e12accc73c539ef79731f59f0a2b6ee760412afb90d5275c8ddedd36b77059d` | 0 | 1.79 | 3325912 | 0 | permitted subset below |
| Asset.lean | 710 | `2c36ba0a589d2e982ca55716f5093e6c5da4152454f24de26c71f9ad9d9ef424` | 0 | 1.60 | 3323420 | 0 | permitted subset below |

Every theorem has a #print axioms command; all 14 final audits pass and all
four final builds have no warnings. `[propext, Quot.sound]` only:
value_reconstruct10_eq, value_range_selector, occupancy_lanes_zero_iff,
asset_selected_iff, asset_selected_add_iff. The remaining 9 use exactly
`[propext, Classical.choice, Quot.sound]`: value_bit_iff,
value_range_zero_iff, value_holds_rows_iff, value_holds_iff,
positive_claim_indices, positive_family_row_claims, positive_holds_iff,
occupancy_holds_iff, asset_holds_iff. No custom axiom or forbidden placeholder.

Raw records: B/evidence/{out,time}-N.log and B/evidence/sha-N.txt. Exit values
above are Lean/scope results, not the outer runner's always-success shell status.
Concurrent commit 839b8cd36 included intermediate G1 Positive/Occupancy files;
its incomplete Occupancy proof is superseded by the final audited source above.
No other job's files or earlier log sections were changed by this job.

### Failed attempts (each followed by a source change)

- 700 Positive: exit 1, 1.48s,3309884KiB,swap 0; norm_num left the Fin84 addition/index projection unreduced; replaced by the small definitional calculation.
- 702 Occupancy: exit 1, 2.15s,3310852KiB,swap 0; broad simp expanded the digest list and split product-zero propositions; replaced with symbolic list lemmas and restricted selector rewriting.
- 703 Occupancy: exit 1, 1.82s,3315884KiB,swap 0; empty-list quantifiers and Fin selector ifs remained; corrected the targeted simp lemmas.
- 704 Asset: exit 1, 1.63s,3308172KiB,swap 0; unknown Bool lemma and unreduced public variant/Option branches; removed the name and explicitly rewrote branch equations.
- 706 Asset: exit 1, 1.58s,3308024KiB,swap 0; rewriting the two-selector lemma failed on embedded Fin casts; first tried explicit functions/selector expressions.
- 707 Value: exit 1, 2.15s,3339432KiB,swap 0; sub_eq_zero rewrote bit residuals before the Boolean lemma; split simplification into two stages.
- 708 Asset: exit 1, 1.56s,3307856KiB,swap 0; explicit functions still did not match embedded Fin casts; changed the goal to the definitionally equal named trace-cell expression before rewriting.
- 709 Value: exit 1, 2.33s,3338176KiB,swap 0; final castAdd/castLE comparison remained after simp; closed only the small index equality definitionally.

Intermediate green checks 701 (Positive,1.54s,3320148KiB) and 705
(Occupancy,1.77s,3326284KiB) were superseded after adding the literal selector
and Family/claim connection, and removing an unused simp argument respectively;
both swap 0. No unchanged failing job was rerun. Failed elaborations are not
accepted proof evidence, and no failed object was consumed.

### Source-region hashes (constants and literal functions)

SHA-256 is over the exact inclusive source lines, retaining their line endings,
at the inspection pin. The full source files are unchanged at the final source
revision. All scalar constants are ordinary K casts; no extension basis is fixed.

| Source | Lines | Region | SHA-256 |
|---|---|---|---|
| T | 59–61 | selector constants | `e8e256aeb01b484860a837dc02f30a7e0534c5b3c0de645cd84b30757501b06e` |
| T | 167–173 | reconstruct_10 | `c4ec02bf072d206729801adaf295e71bb7bf8bb06b99a0a06ac5ea0944b1420c` |
| T | 466–519 | value range/conservation; M31 1024 and 1048576 | `d83d675f5b07e42319c2ad0574f1ab74215419a6699b8084cf439973e1473a24` |
| T | 521–578 | variant output and literal occupancy | `5635178417c64d6c87c482456186de784ef12e2ba46a2f8f29dc5aa54e3abbb2` |
| T | 1121–1141 | scalar_lanes | `c3ac4ed473ba6bb4d73c786ce6dcc12b07436e4216a055174cde9c1408504da4` |
| T | 1165–1181 | asset/amount selectors and caller | `4182d9b5fa97c4cb484a89cc3815e8a2397fc344034cd29c1cf3c875cfc6aa0a` |
| P | 10–12 | ROW, COL, LANE constants | `c974044886464002ffd04e863adf8ea2341b4cf73391547833b3fd6b5d51eb5c` |
| P | 64–70 | residual and selector | `922e71797b43ae9663bcc587320b688094a8ba301655989f4045d6c9264bd499` |

`git diff --check` and the per-theorem audit-command inventory passed.

## G3

Inspection pin `e4d68a70d3f6beb215c9f6dd418f4a2a3740c809`. Source aliases:
P = `crates/aspis-statement/src/poseidon2.rs`;
S = `crates/aspis-statement/src/state_only_poseidon.rs`;
T = `crates/aspis-statement/src/pool_v1/pair_forest_semantic_terminal.rs`;
F = `crates/aspis-core/src/field.rs`. Core and all other family files were unchanged.

### Result and literal scope

`PoseidonConstants.lean` transcribes P:83–104 EXTERNAL_INITIAL (4×16),
P:106–127 EXTERNAL_FINAL (4×16), P:129–132 INTERNAL (14), and P:134
INTERNAL_SHIFTS (15). All 142 field constants are casts into arbitrary
`[Field K]`. A text-level ordered literal comparison with the exact Rust
regions passed. No table was evaluated by a proof.

`Poseidon.lean` preserves the canonical field-operation path P:137–170
(sbox, local matrix and external layer), P:200–218 (full round/internal
layer), and P:339–352 (the explicit 16-word, 4+14+4 permutation evaluation).
It also records P:62–68,239–253,294–308 round classes/pairs and the source
block layout. These are useful algebraic components, explicitly not a
claimed literal port or proved refinement of the projected raw-limb
implementation. A permutation evaluation function is defined; bijectivity
over arbitrary fields is not asserted.

Five proved results: `poseidon_pow5_eq`, `poseidon_block_layout`,
`poseidon_round_pair_layout`, `poseidon_packing_kernel`, and
`poseidon_packing_perturbation`. Layout uses the actual pair-forest 57 blocks
from T:211–216, not S:28's generic 49-block default. Each block's local rows
0–10 hold inputs to rounds `(2r,2r+1)`, row 11 the final output, and row 12
absorption; local row 0 includes the source leading absorption/external
layer. Local rows 0/1 correspond to external-initial pairs 0–1/2–3, local
rows 2–8 to internal pairs 0–13, and local rows 9/10 to external-final pairs
0–1/2–3. Tables stay opaque in these proofs.

### Findings — family stopped

1. **Literal projected Family is outside fixed Core.** T:1253–1255 calls
   `evaluate_state_only_poseidon_oracle_projected` (S:585–617)
   unconditionally, without an audit alternative. It uses `qm31_pack_base4`
   at S:602–603 and raw-limb projected branches S:401–412,504–521.
   `extension_limbs` / `extension_from_raw_limbs` (S:130–140),
   `external_linear_lazy` (S:144–191), `external_local_packed_raw`
   (S:217–267), `internal_linear_lazy` (S:303–329), and base-limb constant
   updates (S:347–357) access a concrete QM31 representation and M31
   reductions. Arbitrary `[Field K]` and Core have no such operations.
   Replacing these by field formulas without a refinement proof is not a
   literal port.
2. **The requested complete component successor iff is false without
   typing.** F:946–989 packs `(v0,v1,v2,v3)` as
   `v0+i*v1+u*v2+i*u*v3`; Core's `Trace K` has unrestricted K-valued cells.
   The nonzero vector `(-i,1,0,0)` has packed value zero, proved by
   `poseidon_packing_kernel`, and adding it preserves any packed output,
   proved by `poseidon_packing_perturbation`. This is a defect in the
   unrestricted requested statement, not a claimed attack on the
   base-typed Rust trace.

Global Poseidon row quantification does not remove the obstruction. Start
with a trace satisfying the ordinary round recurrence and alter columns
0/1 at block 0's final local row 11 by `-i` / `+1`. Row 10's packed successor
remains unchanged; row 11 has no active selector. Row 7 can read row 11
through xor12 only in the leading branch, whose local-0 weight is zero at
row 7. No other selected successor reads row 11. Thus the packed family
remains satisfied while row 10's sixteen-word successor equality fails.
This support argument is source inspection; no nonexistent Core Family
theorem is asserted.

Smallest interface alternatives, for the lead only: (a) explicitly choose
an unpacked scalar Family and separately prove its base-typed equivalence
to the source packed terminal; or (b) supply a concrete tower/packing and
limb-refinement interface plus base-subfield typing and packing injectivity
on that subfield. Adding a basis alone is insufficient for arbitrary
K-valued traces. Neither alternative was added as a premise or selected
here. `poseidonFamily` and `poseidon_holds_iff` are intentionally absent.

### Build evidence

Same pinned host/lake environment and LEAN_PATH as G1; `run.sh` using
`objects/`, `-j1 -M4500 -DElab.async=false`, MemoryHigh=5G, MemoryMax=7G,
MemorySwapMax=0, TasksMax=128, timeout 900 s. Before each run the exact
populated-scope reservation loop from run2.sh was applied with
`+7 GiB <= 55 GiB`; each admitted 24+7. One G3 job at a time, no cap
increase, no dependency rebuild. Raw records are workspace
`evidence/{out,time}-900/901/902/903.log` and `sha-N.txt`.

| File | Attempt | SHA-256 | Exit | Wall s | Peak RSS KiB | Swaps | Axioms |
|---|---:|---|---:|---:|---:|---:|---|
| PoseidonConstants.lean | 900 | `c87e94b63a575b96cecff98eea6a84385945d5481054a688d24ba162452340b0` | 0 | 1.50 | 3310196 | 0 | definitions only |
| Poseidon.lean, group focused pass | 902 | `b936cb8249d536849387622b837af2042a457eafbdfb2d9a703470b64649178a` | 0 | 1.93 | 3335184 | 0 | permitted subset below |
| Poseidon.lean, coordinator check | 903 | `b936cb8249d536849387622b837af2042a457eafbdfb2d9a703470b64649178a` | 0 | 1.93 | 3335040 | 0 | permitted subset below |

`poseidon_pow5_eq` and `poseidon_packing_perturbation` use
`[propext, Quot.sound]`. The other three theorems use
`[propext, Classical.choice, Quot.sound]`. Each theorem has its own
`#print axioms`; final builds have no warnings. No concrete Finset.univ or
1024-row enumeration; only symbolic Fin bounds and small round-number
arithmetic. The coordinator independently compared the source constants
in order (64+64+14 match), inspected the canonical field-operation
definitions, and ran the focused lead audit 903 required by AGENTS.md.

Failed attempts:

- 901 Poseidon: exit 1, 1.84 s, 3322904 KiB, swap 0; reserved word `local` used as a binder and final Nat addition association left open; renamed the binder, used Fin.val_castLE and omega. Failed elaboration was not accepted and no failed object was consumed. Attempt 902 followed this source change.

`git diff --check` passed.

### Exact source-region SHA-256s

Hashes include the inclusive line ranges and line endings at the inspection pin.

| Source | Lines | Region | SHA-256 |
|---|---|---|---|
| P | 83–104 | EXTERNAL_INITIAL | `52abaf623026228d1b36fa76087eb2602cd61b0e98631777786c4a7c4bd08454` |
| P | 106–127 | EXTERNAL_FINAL | `e275b74c1f8a96cd2379cb1b1d7f786dffae4144668b602199334485e922c9a1` |
| P | 129–132 | INTERNAL | `f149c66e7e6ab405edc31af5bd85b11afdbc872fe64d46aa26fff497b8fae323` |
| P | 134 | INTERNAL_SHIFTS | `0498beff372384d7b4fb3a2739789fa0d53ec0700aa26d92f239a61f2e7f2534` |
| P | 137–170 | canonical sbox/external layer | `088789848cad15005cc002ccffd39c05886f3a87cd36ea7dda057733ec344aac` |
| P | 200–218 | canonical full/internal layers | `65e75e9d75b9600a0485f715ba8f67c370a9fffb5bfc5f33ef329a5e908d4cca` |
| P | 339–352 | canonical permutation | `5edb9f05a8a0627912cacf8a164b1d33c44f5c0ac115efe4edac6f26255f779d` |
| S | 585–617 | stopped projected evaluator | `3e5ea528ddaf46ce11d5034f2481b11dde13085b77ce5671dee8cfe26b4e90c6` |
| F | 946–989 | stopped tower packing | `9af6b08676d1fe345894c9789a515f18530f0567fea6d59c504718ed23e2d183` |
| T | 211–216 | actual 57-block selector | `5419a950c6b3fa09512bb362bd321ba81277704cdd92d1ee7175e142b4923e0e` |

### Continuation G3′ — endpoint iff obstruction

Resumed from lead interface commit
`dae112e8f7f8f08d8b06272464a7daefb978dffe` after fetch/fast-forward.
CoreExt's base typing and independent packing basis resolve the original
interface gap for the authorized canonical field model. The lead's separate
Rust-to-model refinement obligation for S:130–357,401–617 remains explicit.
Core, CoreExt, constants and all preexisting function bodies are unchanged.

**New exact stop:** a round-by-round relation on a fixed committed trace is
not equivalent to its block endpoint equations alone. S:389–398 adds local
row 12 into the low eight words of local row 0, applies the external layer,
then initial full rounds 0 and 1. S:589–615 selects that successor equation
at local row 0. P:339–352 specifies the full canonical permutation; the
pair-forest caller uses all 57 blocks (T:211–216).

`poseidonLeadingPair` and `poseidonAbsorbedInput` record those canonical
field operations. `poseidon_endpoints_do_not_imply_successor` proves an
explicit counterexample over every field: every block output at local row
11 is the canonical permutation of its absorbed input, yet block 0's local
row 1, word 0 differs from the required leading-pair output by one. The
witness has zero input and absorption rows, opaque `poseidonPermutation 0`
at output rows, and the perturbed first intermediate cell. No permutation,
constant table or finite universe is evaluated. Bare local row 0 also needs
the low-eight-word absorption when stating the endpoint result.

The smallest correction is to request the forward endpoint implication for
this trace, or an iff with the complete intermediate-round catalogue. An
endpoint iff could instead quantify existence of appropriate intermediate
states. Choosing or applying one of these statement changes is left to the
lead; no Core/CoreExt change is needed for this obstruction. No
`poseidonScalarFamily`, `poseidon_scalar_holds_iff`, or packed/scalar theorem
is claimed past this stop. No tuple, multiset or probabilistic claim is made.

Focused development and independent coordinator review both passed on the
frozen `Poseidon.lean` SHA-256
`57ab72400b97b7918f08dd1d2ab186dd25dd3c4b61c496b09bf51b050a1a31db`:

| Target | Attempt | Scope/Lean exit | Wall s | Peak RSS KiB | Swaps |
|---|---:|---:|---:|---:|---:|
| R0P/Poseidon, focused | 904 | 0 | 2.22 | 3342084 | 0 |
| R0P/Poseidon, coordinator | 905 | 0 | 2.13 | 3342360 | 0 |

Both runs used the existing host workspace and Lean 4.32.0 cache,
`run2.sh N R0P/Poseidon 7000 7`, `-j1 -M7000 -DElab.async=false`, timeout
900 s, MemoryHigh=5G, MemoryMax=7G, MemorySwapMax=0 and TasksMax=128.
Reservation admitted 24+7 GiB below 55. Raw evidence is
`evidence/{out,time}-N.log`, `sha-N.txt`, and `source-N.lean` in
`/home/dombarker/project-offloads/aspis-fs-generic-20261006/` on
`dombarker@100.108.41.90`. Actual scope and time exit statuses were inspected.
There were no failed G3′ attempts or warnings. All six theorems have
`#print axioms`; every result uses only a subset of `propext`,
`Classical.choice`, `Quot.sound`, including the new counterexample.
Coordinator source review and `git diff --check` passed. No cap increase,
local build, dependency rebuild or replay of unchanged original G3 was used.

## G4

Inspection pin `e4d68a70d3f6beb215c9f6dd418f4a2a3740c809`. Only Copy.lean
and CopyConstants.lean changed; Core and other groups were untouched.
Source T is `crates/aspis-statement/src/pool_v1/pair_forest_copy_terminal.rs`;
C is `pair_forest_copy_terminal_constants.rs` in the same directory.
All definitions are over arbitrary `[Field K]`, with M31 constants cast from
naturals. No extraction or LogUp-to-tuple-equality implication is asserted.

### Port and finding

**The Copy Family and complete Holds equivalence stop at Core's input
interface.** T:910–918 explicitly receives H1 (`h1_z`), lambda and chi;
T:1068–1071 uses `active * copy_residual(row,h1_z,chi)`. Core.Openings
exposes only columns 0–15 at three points, although Trace has 29 columns
and H1 is column 26. Core.Public contains no lambda/chi. Fixing these
inputs, capturing an arbitrary helper trace, or replacing the source
residual by endpoint equality would not be a literal Family on the same
Trace. No `copyFamily` or `copy_holds_iff` is claimed. Smallest interface
direction for the lead: add a current-row H1 opening read from `A 26 b`,
and expose lambda/chi explicitly in the Family/Holds challenge context
(or explicitly parameterize the family by fixed challenges). Neither the
interface nor relation was changed.

Independent deliverables are complete: literal full constant arrays;
producer/consumer tagged 16-tuples for every generated link, including
offsets and zero limbs; source linkWeight; explicit-input selector/active,
compression, endpoint accumulation, denominator/numerator residual and
evaluator helpers. `copy_positivity_links` proves the actual registry
contains the four named entries, enabled for every variant and append
index, with exact cells `(1008,10)→(1014,0)`, `(1010,10)→(1014,1)`,
`(1012,10)→(1015,1)`, `(1014,2)→(1015,0)` and all remaining 15 limbs zero.
It does not assert endpoints equal or infer equality from LogUp.

Production selection: all audit optimizations off. Ported `active_literal`,
not `active_mask_basis`; `pattern_values_literal`, not
`pattern_values_windowed`; literal endpoint accumulation, not selector-cache,
binary-weight, pattern-basis, selector-tensor or finish-dot audit variants.
Source ranges: T:79–103 descriptor structures; T:118–135 mask-sum loop;
T:137–141,173–191 selector and active; T:232–263 compression; T:331–377
row residual and link weights; T:423–450 endpoint accumulation;
T:910–972,1048,1068–1072 evaluation. Selector expansion from an off-domain
point is outside the explicit-selector evaluator's interface and is not
claimed here.

`COPY_LINKS` is represented as original prefix ++ named four-entry block ++
original suffix, retaining every record's source order. Membership treats
the large neighboring blocks abstractly. Patterns 6–9 are literal singleton
arrays stored as first-cell/zero-tail functions; their exact arrays are
documented beside the definitions. The dispatch exposes those named entries
before other cases. Thus all pattern proofs are symbolic in limb i, and no
global array, 16-element vector, 1024-row range or finite-field universe is
evaluated by tactics. The `rfl` steps close only tiny Fin casts and record
fields after symbolic rewriting. Mask bit iteration and link iteration
retain increasing/source order; residual field operations are unsimplified.

A read-only Python comparison matched all 64 active masks, 64 inactive
groups, 7 inactive masks, 14×3×16 pattern entries and 136 link records
(order, tags, weights, levels and endpoint fields). The lead independently
repeated the comparison: all 64+64+7 array entries, 672 pattern cells and
136 original-order links match. These are transcription checks, not Lean
proofs of runtime refinement. The lead also completed source review of the
explicit-input helpers and four-link theorem, including value accumulation
when link weight is zero and the active-mask complement branch.

### Final compile evidence

Same pinned host/lake environment and captured LEAN_PATH as G1.
CopyConstants uses run.sh (`objects/`, `-j1 -M4500 -DElab.async=false`);
Copy uses run2.sh ... 7000 7 (`objects2/`, `-j1 -M7000 -DElab.async=false`).
The existing `objects2/R0P` symlink points to `objects/R0P`. Both scopes use
MemoryHigh=5G, MemoryMax=7G, MemorySwapMax=0, TasksMax=128 and timeout 900 s.
The explicit populated-finite-cap reservation before run.sh and the runner
reservation for run2 admitted 24+7 GiB under 55. One G4 job at a time;
no cap changes or dependency rebuilds.

| File | Attempt | SHA-256 | Exit | Wall s | Peak RSS KiB | Swaps | Axioms |
|---|---:|---|---:|---:|---:|---:|---|
| CopyConstants.lean | 1001 | `cca9bdd0d2988693652d23010e068155abe0bc52fe36d030dbd8c163fe4f4f68` | 0 | 1.96 | 3348732 | 0 | definitions only |
| Copy.lean, group focused pass | 1004 | `98c98df8e2b2c545cf47ead0c5f47a77fe7da5170399f4d98cfdbcdf0e9e0352` | 0 | 1.90 | 3333608 | 0 | permitted subset below |
| Copy.lean, coordinator check | 1005 | `98c98df8e2b2c545cf47ead0c5f47a77fe7da5170399f4d98cfdbcdf0e9e0352` | 0 | 1.81 | 3333544 | 0 | permitted subset below |

`copy_linkWeight_zero`, `copy_singleton_patterns` and
`copy_positivity_links` use `[propext, Quot.sound]`;
`copy_positivity_mem` uses `[propext]`. Every theorem has `#print axioms`;
final files have no warnings or placeholders. The coordinator check 1005
used run.sh at the lower -M4500 limit, with the same 7 GiB scope and admitted
24+7 reservation; it supplies the focused lead check required by AGENTS.md.
Raw records are workspace `evidence/{out,time}-100N.log` and `sha-100N.txt`.
Lean exit is taken from scope output, not the outer runner shell exit.
`git diff --check` passed.

### Attempts

- 1000 CopyConstants: green, 2.02 s, 3349004 KiB, swap 0; superseded by the sparse pattern representation before any dependent proof.
- 1002 Copy: exit 1, 1.90 s, 3318140 KiB, swap 0; symbolic tuple rewrites left tiny Fin casts; added only small definitional closure and removed an unused simp entry.
- 1003 Copy: exit 1, 1.77 s, 3318492 KiB, swap 0; four-entry membership left the final empty-list alternative; added List.not_mem_nil/or_false and removed an unused simp entry.

No unchanged failed job was rerun; no failed elaboration was consumed as
evidence.

### Constant-region SHA-256

Hashes are exact inclusive source lines with original line endings at the
inspection pin.

| C lines | Region | SHA-256 |
|---|---|---|
| 5 | ACTIVE_ROW_MASKS | `a084c4322be561781f1ae55e7634a33cbff18df6c082a486ada0985b11b762b2` |
| 7 | INACTIVE_ROW_GROUPS | `e9bc8dceaa5ea0402bb41abad7b395b167769792b94540a5ae45de463c5cac7b` |
| 8 | INACTIVE_GROUP_MASKS | `60b45c4077023530f7ca899e81c09a93edf492929f2b862d4e79faec5992bee5` |
| 10–25 | COPY_PATTERNS | `049361cce80ce94b016e40afabba2db28e396ee090659609e7880735abd86737` |
| 27–164 | COPY_LINKS | `46187e7618fcba23fabf27f20e7f892ca5e4df38ab619ad84f238bf10ffc4e71` |
| 42–45 | Four positivity links | `46ffb4e8785c6d6745b071256f1fd5750aed526da9dffff30ba40f67df398e9e` |


### Continuation G4′ — complete challenge-dependent row equivalence

Resumed from `dae112e8f7f8f08d8b06272464a7daefb978dffe` after
fetch/fast-forward. The lead's `CFamily`/`CHolds` resolves the original
Copy interface stop: lambda and chi are explicit parameters and H1 is
exactly the same trace's `A 26 b`. `copyFamily` now emits the sole literal
`active * copyResidual row h1 chi` from T:910–972,1048,1068–1072.
The existing explicit-input helpers, five constant tables, positivity
links, Core, CoreExt and all G1/G2 files remain unchanged.

`copy_holds_iff pub lam chi A` proves the complete pointwise condition:
on each literal active row, with producer slots `p0,p1`, consumer slots
`c0,c1` and their accumulated weights, define
`Dp=(chi-p0)*(chi-p1)`, `Dc=(chi-c0)*(chi-c1)`,
`Np=pw0*(chi-p1)+pw1*(chi-p0)` and
`Nc=cw0*(chi-c1)+cw1*(chi-c0)`. The plain field equation is
`Dp*(A26(b)*Dc+Nc)=Dc*Np`. Each slot value is the source-order sum over
its link endpoints of `tag + Σ_j lambda^(j+1)*tuple_j`; the tuples use
those endpoints' trace cells, pattern offsets and prescribed zero lanes.
The list retains multiplicity and values remain present even when a link's
weight is zero. No uniqueness assumption or denominator nonzero premise is
introduced, and no division is performed.

Symbolic fold lemmas establish iterative powers, pattern compression and
producer/consumer accumulation before rewriting the row equation. The
active-mask proof uses arbitrary-mask bit facts, nodup filtered selectors
and a single selected high block. It evaluates no mask table, large range
or concrete finite universe. The existing G2 high/low adapter is reused
only on Boolean rows. `copy_inactive_residuals` proves that inactive rows
emit exactly `[0]`, without imposing H1=0 there.

The two aggregate identities refer to the actual pair-forest semantic
terminal, `pair_forest_semantic_terminal.rs:1307–1308`:

- `copy_mu_helper_sum`: `Σ_b mu*H1(b) = mu*(Σ_b H1(b))`.
- `copy_mu_inactive_helper_sum`:
  `Σ_b mu*mu*((1-active(b))*H1(b)) = mu*mu*(Σ_{b∈I} H1(b))`,
  where `I=copyInactiveRows` is the literal inactive mask set.

These identify the sums checked through the mu terms; they do not assert
either sum vanishes. No tuple equality, multiset balance, challenge
soundness or full SEM closure is derived. There is no remaining G4′
source/interface stop within this requested scope.

The coordinator rechecked T:910–972,1048,1068–1072 and the terminal's mu
terms against inspection pin `e4d68a70d3f6beb215c9f6dd418f4a2a3740c809`.
Those Rust files and Copy constants are byte-identical at the lead revision.
The earlier table/source-region hashes above remain applicable. CoreExt
matches lead build 606 SHA-256
`de191f5bf4ca0389c7b9e0ee613982888a97ec9810072913c19054882364e56b`;
its cached object was reused without rebuilding dependencies.

Final `Copy.lean` SHA-256:
`28a37fcfab1c2a6235e42932d44156c7952e6311958317ce843adb9737709d0f`.
All continuation builds target only `R0P/Copy`, on
`dombarker@100.108.41.90` in
`/home/dombarker/project-offloads/aspis-fs-generic-20261006/`, using pinned
Lean 4.32.0 and `run2.sh N R0P/Copy 7000 7`. The existing objects2/R0P
symlink/cache was reused. Scopes set MemoryHigh=5G, MemoryMax=7G,
MemorySwapMax=0, TasksMax=128; Lean uses `-j1 -M7000 -DElab.async=false`
and timeout 900 s. Each reservation admitted 24+7 GiB below 55; one G4 job
at a time, no cap changes, local builds or package/dependency rebuilds.

| Attempt | Scope/Lean exit | Wall s | Peak RSS KiB | Swaps | Result/change before next attempt |
|---:|---:|---:|---:|---:|---|
| 1006 | 1 | 2.28 | 3334484 | 0 | Signed-fold rewrite order, mask indicator rewrite, sum definitional closure and active conditional; proofs corrected. |
| 1007 | 1 | 2.31 | 3331708 | 0 | Nonzero-mask conditional needed explicit rewrite. |
| 1008 | 1 | 2.38 | 3332596 | 0 | Removed redundant closure; update-at-self branch needed `if_true`. |
| 1009 | 1 | 2.49 | 3335436 | 0 | Four projection applications needed explicit higher-order arguments. |
| 1010 | 0 | 2.70 | 3358280 | 0 | 24 audits, symbolic helpers green; final bridge and sums added next. |
| 1011 | 1 | 2.87 | 3339300 | 0 | Generic `congr 1` hit recursion depth in aggregate proof; replaced by explicit `congrArg`, removed unused field instance. |
| 1012 | 1 | 2.88 | 3341652 | 0 | Aggregate branch simplification made no progress; replaced with explicit conditional rewrites. |
| 1013 | 0 | 2.95 | 3365140 | 0 | Complete file, 32 audits, no warnings. |
| 1098 | 0 | 2.99 | 3365140 | 0 | Frozen coordinator check, 32 audits, no warnings. |

Attempt source SHA-256s (1013 and 1098 use the final hash above):

| Attempt | SHA-256 |
|---:|---|
| 1006 | `b921a38c8c0045d77845502bf52e0dc9085cbb1849bde2fa9ee4958d269009b7` |
| 1007 | `e41b70ed507ba6db84c766f9d98409dbff9038b759cdb4bacb635e69e0a5478d` |
| 1008 | `28e62c395028cda24631bff911f47a84d6f4c85e2c96fd157323ea4826785eee` |
| 1009 | `d21cd73f9edc7467abf71bf149a4072f1e6acb5a153372e99679ad194395c2dc` |
| 1010 | `7aa83bea0de19818818bf4249281f55045cfd43c1a4fc9adcf488e0444ac92c7` |
| 1011 | `6a4c97d9e151e79e42c53c2b59d25698730f97d3b610b740d83287e9afd7e601` |
| 1012 | `3b98a39550349aada9d5a60c59016b925f0906c1b0cfdaf665c963afa266141d` |

Raw evidence is `evidence/out-N.log`, `time-N.log`, `sha-N.txt` in the
host workspace; final sources are also preserved as `source-1013.lean`
and `source-1098.lean`. Actual scope/Lean and time exit statuses were
inspected; the outer runner's success was not used to classify failures.
No unchanged failing attempt was rerun and no failed elaboration was used
as proof evidence. All 32 theorem declarations, including private helpers,
have matching `#print axioms` commands and use only subsets of `propext`,
`Classical.choice`, `Quot.sound`. The final diff has no forbidden proof
terms/options or warnings. Coordinator source review, frozen focused check
and `git diff --check` passed; unrelated untracked work was preserved.

## G2

**Completed scalar row equivalences.** Inspection pin
`e4d68a70d3f6beb215c9f6dd418f4a2a3740c809`. Schedule, Path and Digest now have
complete, compiled `Holds` equivalences; EmptyRoots compiles. Schedule retains
all initial and absorption residuals and all prescribed zero cells. Core,
G1, G3 and G4 are unchanged; the recorded Poseidon/Copy stops remain in force.

The prior session lost SSH access (`Operation not permitted`) and GitHub DNS
after failed820. This resume verified ordinary SSH and GitHub access before
any build. No alternate network route or local compilation was used. Final
coordinator checks898/899 passed sequentially after the sources were frozen.
The final source snapshot is base revision
`cd91bc7946e27985abce1c204c52cfa93f99d2ae` plus the four G2 sources identified
by their SHA-256s below; this log is committed with that exact G2 snapshot.

### Literal ports and source correspondence

T = `crates/aspis-statement/src/pool_v1/pair_forest_semantic_terminal.rs`;
C = `crates/aspis-statement/src/pool_v1/pair_forest_copy_terminal.rs`;
E = `crates/aspis-statement/src/pool_v1/pair_forest_semantic_terminal_constants.rs`.

| File / family | Source ranges | Status and complete condition |
|---|---|---|
| Path / `pathFamily` | T:156–164,394–427; C:138–176 for high/low selector layout | **Proved** `path_holds_iff`: blocks 57–62, local rows 1,5,9,13; bit Boolean residual and all eight left plus eight right successor equations. The source's 17 lane order and multiplication order are retained. |
| Schedule / `scheduleFamily` | T:218–334,382–391; `spend.rs`:14–16; `poseidon2.rs`:57 | **Proved** `schedule_holds_iff`: initial rows (local0) impose the complete domain/length/zero catalogue on full-initial blocks and all eight rate zeros on node blocks; absorption rows (local12) impose every zero cell selected by `ScheduleAbsorbs`, for both variants. All32 scalar slots are retained. |
| EmptyRoots | E:2–24; T:175–178,654–661; `poseidon2.rs`:465; `aspis-core/src/field.rs`:55–59 | All 21×8 constants transcribed as Nat literals. Table remains irreducible in proofs. Right-target preprocessing preserves source M31 addition before the K cast. |
| Digest / `digestFamily` | T:364–380,609–694; `pair_tree_profile.rs`:401 for public u64 index | **Proved** `digest_holds_iff`: anchor at row907, nullifier427, present recipient475, change523; all20 frontier levels at `(34+level)*16+0` columns8–15 on zero append bits, or local row12 columns0–7 on one bits; next root859; conditional carry frontier at `(33+carry)*16+11`. |

The selected production paths are the literal non-semantic-factor-audit and
non-packed-digest-audit paths. The alternative factored paths T:336–359 and
429–463, and packed digest path from T:696, are not selected. The scalar
Family outputs are before extension packing; these files establish neither
packing equivalence nor extraction.

Core.Sel contains row weights only, while the Rust Schedule and Path routines
also read high[64] and low[16]. The lead approved a Boolean-row adapter:
`g2High sel h = sum_l sel(16*h+l)` and
`g2Low sel l = sum_h sel(16*h+l)`. The compiled symbolic lemmas prove that at
`rowSel b` these are respectively `[h=b/16]` and `[l=b%16]`. The literal
high/low multiplications are retained. This is not an assertion of equivalence
for arbitrary off-domain selector inputs. The ordered sum_high loop is a
left fold; Schedule's node selector uses one accumulator over the concatenated
ranges 4..25 followed by 33..57, rather than two independently reset sums.
Off-support proofs ultimately use `rowSel_ne`. No table or 1024-row range is
evaluated by a proof, and no concrete State/Addr/Wide finite universe occurs.

Digest preserves the eight-lane accumulator's call order, including the
20-level loop and the final conditional carry call. `digest_rows_pairwise`
proves distinct enabled calls have distinct Boolean rows, so the accumulated
residual cannot cancel between separate public bindings. It does not establish
any probabilistic relation. The carry adapter scans at most twenty low bits
of Core's Nat index; this is the observed part of the source's
`min(u64.trailing_ones(index),20)`. Its bound is proved symbolically. No new
append-index validity premise or UInt overflow assumption is introduced.

### Findings retained without changing the source

1. **Recipient presence is the literal guard.** T:631 tests
   `public.recipient: Option<Digest>`, not `public.variant`. Core permits a
   present recipient in either variant. `digest_holds_iff` therefore uses the
   exact Option-presence condition. The brief's wording “for transfer” requires
   a separate public-constructor invariant, which is not assumed here.
2. **M31 right-tweak addition precedes lifting.** T:375 adds the tweak
   `0x41531005 = 1095962629` to the last digest limb as M31. A K-level addition
   of the cast literals would be wrong over an arbitrary Field K when the sum
   wraps. The actual true-tweak calls use only frozen empty roots; the port
   specializes those calls and preserves `let s := root+tweak; if s >= p then
   s-p else s` in Nat before casting. Levels 0,2,3,4,9,10,11,12,14,15,16,17 wrap.
   Other lanes are cast unchanged, with no extra reduction. No CharP premise
   is added, and no generic right-tweak operation on arbitrary Digest K is
   claimed to represent the unavailable M31 representation.
3. **Schedule has no established source obstruction.** The full row catalogue
   is proved without changing any literal definition or original theorem
   statement. `schedule_low_zero` and `schedule_low_twelve` reduce tiny Fin
   selector projections to Nat truth facts. The final exceptional initial
   proofs precompute high-selector values and the zero node selector, then
   split the low-row and lane cases before simplifying the field formulas.
   Absorption uses explicit lane regions below2, below8, and the remaining
   lanes. The final proofs use no broad `simp_all`, trace-cell arithmetic search, new premise,
   limit increase, table normalization or row enumeration.

The coordinator compared all original definition and theorem headers with
the failed820 snapshot: every literal/catalogue definition and original
statement is unchanged. The two new selector helper statements add no
premises. Frozen Path/Digest/EmptyRoots hashes and all non-G2 Lean files were
also checked unchanged. The complete Schedule proof diff was reviewed before
coordinator898; the source formulas and ordered residual catalogue were
checked against the inspection pin.

### Build environment and final evidence

Host/workspace, pinned Lean4.32.0 and captured lake environment are as in G1.
Pre-resume G2 attempts used `run.sh N R0P/File`, reusing Core/Mathlib and the
small group dependency objects in the existing `objects/` mirror. Each launch
was preceded by an explicit populated-cgroup MemoryMax reservation check
against 55 GiB (observed reservations 24 or26 GiB plus7 GiB). The runner used
`-j1 -M4500 -DElab.async=false`, MemoryHigh5G, MemoryMax7G,
MemorySwapMax0, TasksMax128, timeout900s. One G2 Lean job at a time; no cap
increase and no unchanged failed job rerun. LEAN_PATH composition is the G1
`objects/` mirror plus the captured pinned lake paths.

Resumed development821–832 and final lead checks898/899 use the prescribed
`run2.sh N R0P/File 7000 7`: `-j1 -M7000 -DElab.async=false`, MemoryHigh5G,
MemoryMax7G, MemorySwapMax0, TasksMax128, timeout900s. `objects2/R0P` was
verified to point to the existing `objects/R0P`; no dependencies were rebuilt.
Every resumed launch admitted 24+7 GiB under the 55 GiB reservation ceiling.
Final832,898,899 all have zero warnings.

| File | Attempt | SHA-256 | Exit | Wall s | Peak RSS KiB | Swaps | Axioms / status |
|---|---:|---|---:|---:|---:|---:|---|
| Path.lean | 805 | `bb8ecd5b7b3880bd6cdf71ec06c6066195ce9a25b532111a21b861cc5833cb79` | 0 | 4.78 | 3340740 | 0 | all6 audits permitted; no warnings |
| EmptyRoots.lean | 803 | `648c9aaccf1691b634b2a91f46348ecb1e2d7382a982dcbddff1dcc786b77cbc` | 0 | 1.48 | 3310664 | 0 | definitions only |
| Digest.lean | 819 | `928d531c7ae80fdb2a3865bf3b2eac2d1dea84c2892c413f5c4a63709947d26b` | 0 | 8.47 | 3382096 | 0 | all13 audits permitted; no warnings |
| Schedule.lean, final development | 832 | `393e5edd57671f64647056130ea5b184a65dabb2b0069c45b1cf9afa1f058fb6` | 0 | 13.81 | 3435624 | 0 | all31 audits permitted; no warnings |
| Schedule.lean, coordinator check | 898 | `393e5edd57671f64647056130ea5b184a65dabb2b0069c45b1cf9afa1f058fb6` | 0 | 13.81 | 3433612 | 0 | all31 audits permitted; no warnings |
| Digest.lean, coordinator check | 899 | `928d531c7ae80fdb2a3865bf3b2eac2d1dea84c2892c413f5c4a63709947d26b` | 0 | 08.09 | 3381620 | 0 | all13 audits permitted; no warnings |

Path's `g2_fold_add` uses `[propext, Quot.sound]`; its other five theorems use
`[propext, Classical.choice, Quot.sound]`. Digest's
`digest_trailing_ones_le`, `digest_carry_le`, `g2_row_sum_off`,
`g2_row_sum_at`, `g2_row_sum_iff`, and `digest_fold_eq` use
`[propext, Quot.sound]`; its other seven use
`[propext, Classical.choice, Quot.sound]`. Every theorem has an explicit
`#print axioms` command. All31 Schedule theorems, including every private
helper, use exactly `[propext, Classical.choice, Quot.sound]`. Thus all50 G2
theorem declarations have matching explicit audits. Failed compiler-generated
error terms and failed audits are not proof evidence; no failed object was
used as a dependency. No source contains a placeholder or custom axiom.

Raw evidence remains at the build workspace's
`evidence/{out,time}-N.log` and `evidence/sha-N.txt`. Exit status is the Lean/
scope status, not the runner's outer shell status. The coordinator reconciled
both the scope `exit=` and `/usr/bin/time` exit fields with local/remote source
hashes. Schedule is frozen at832/898's hash, and Digest remains at819/899's
hash. The previously handed-off Schedule hash
`d53513e65b28c6054755dd964092316c7b28d4e0da7698cbe207c8db196b9323`
was exactly failed820 and was not rerun unchanged.

### Failed attempts (one line each)

- 800 Path: exit1,3.80s,3318884KiB,swap0; missing decidability for the PathRow conditional; changed it to an abbreviation.
- 801 Path: exit1,4.56s,3323256KiB,swap0; final conjunction association and Fin casts did not match the plain-cell statement.
- 802 Path: exit1,4.62s,3321944KiB,swap0; association was corrected, but definitional cast conversion remained.
- 804 Path: exit1,4.59s,3323196KiB,swap0; convert generated tiny cast/association goals; added explicit definitional closure.
- 806 Schedule: exit1,21.54s,3414728KiB,swap0; simultaneous conditional simplification reached default heartbeats; separated selector/proof structure.
- 807 Schedule: exit1,36.77s,4689732KiB,swap0; unsupported progress tactic and excessive elaboration normalization hit the existing kernel memory check; replaced tactic and made selector definitions locally irreducible.
- 808 Schedule: exit1,1.62s,3314732KiB,swap0; dsimp did not unfold locally irreducible definitions and conjunction proofs needed type annotations; used explicit unfolding.
- 809 Digest: exit1,6.55s,3339788KiB,swap0; list membership/nodup, row injectivity, induction binder and final equation packaging needed explicit proofs.
- 810 Schedule: exit1,22.58s,3395144KiB,swap0; broad scalar conditional proof still reached default heartbeats; split the support cases.
- 811 Schedule: exit1,24.03s,3429824KiB,swap0; combined support case proof remained over the default heartbeat budget; introduced separate named row-block helpers.
- 812 Schedule: exit1,75.22s,3420128KiB,swap0; symbolic casts and unresolved impossible branches remained, and variable-range helpers reached default limits; narrowed simplification.
- 813 Digest: exit1,5.86s,3344464KiB,swap0; tiny row numerals, no-progress simp, and final Fin/zero-add casts remained; normalized only small indices and rewrote the final proof by cases.
- 814 Schedule: exit1,72.80s,3439040KiB,swap0; restricted simplification left contradictory not-True branches and further default-limit failures; isolated a focused diagnostic target.
- 815 Digest: exit1,8.20s,3353824KiB,swap0; only final castLE wrappers remained; explicitly simplified those small constructors.
- 816 Schedule: exit1,4.48s,3331100KiB,swap0; focused block1 diagnostic exposed not-True branches; no partial diagnostic source was retained.
- 818 Schedule: exit1,73.01s,3435464KiB,swap0; variable node/off proofs still reached default limits; replaced them by symbolic high=0 and nodes=1/0 facts.
- 820 Schedule: exit1,27.54s,3408972KiB,swap0; node/off default-limit failures were removed, but low-selector numeral projections, selected absorption equations and initial block0 simplification remain unresolved; next check blocked by changed network permissions.
- 821 Schedule: exit1,24.95s,3411272KiB,swap0; a new helper incorrectly inferred local row0 from block0; replaced by a modulo-row case split.
- 822 Schedule: exit1,25.23s,3414972KiB,swap0; low-selector Nat equality orientation/casts and lane goals remained.
- 823 Schedule: exit1,25.18s,3413828KiB,swap0; block0 repaired, initial-node low selector and absorption lane cases remained.
- 824 Schedule: exit1,25.39s,3414656KiB,swap0; initial-row proof passed, absorption lane-support cases remained; replaced broad tails by explicit lane regions.
- 826 Schedule: exit1,21.67s,3402160KiB,swap0; warning cleanup removed necessary Fin/support simplification; repaired in827.
- 829 Schedule: exit1,22.07s,3402664KiB,swap0; another warning trim left impossible initial-block25/27/30 branches. The worker's purported green828 backup actually had829's hash. Coordinator rejected that label, reconciled raw evidence, and replaced all seven exceptional initial proofs with explicit selector facts in830.

### Resumed development hashes and superseded passes

All rows below target `R0P/Schedule` using run2 and the base revision above.
Swaps were0 throughout; exit is the Lean/scope result. Raw `sha-N.txt` and
`out-N.log` identify each exact source and audit output. Failed rows are not
accepted proofs.

| Attempt | SHA-256 | Exit | Wall s | Peak RSS KiB | Audits | Warnings |
|---:|---|---:|---:|---:|---:|---:|
| 821 | `62d18b473bd44668ea6adbc1e5ee01cd43ed795bc9769d873c976dad0fd2e54c` | 1 | 24.95 | 3411272 | 29 | 197 |
| 822 | `803bd9900cde6f73e33316ed3e7eae6cdd9bfdfc0cca6922ca359828bd5c456f` | 1 | 25.23 | 3414972 | 29 | 202 |
| 823 | `994d2057dcfcaa4d4df8fc3266dceec1b8f247f2927b61c44975ef7f8be681db` | 1 | 25.18 | 3413828 | 29 | 202 |
| 824 | `3edef1d353474608cfcff806d3c9c14643ccd3c5cd0917720b857a383f413e2a` | 1 | 25.39 | 3414656 | 29 | 175 |
| 825 | `c632897d29228a9eb05fae70b3ea019b8b92c71b43516154ae3610c93a22aae8` | 0 | 22.55 | 3438032 | 29 | 144 |
| 826 | `56d6bdd0218eb69e2eaf02ba176f68be1fc3782b4c7be51a515e9ccab38f3cbe` | 1 | 21.67 | 3402160 | 31 | 22 |
| 827 | `310cff9ed242318503fc5d3d851b59913a7cf253b3f3be836f7a334875d1f352` | 0 | 22.58 | 3444136 | 31 | 127 |
| 828 | `a1f6eeb29443daa8d10f718f443197f4fd66ac6a6ee431e71d683334e78a4dbe` | 0 | 22.64 | 3446504 | 31 | 117 |
| 829 | `3fd3d01ec7b71efc14cd2cafe3fa19278b0f9979b94c7df32f8f4a3a0508253a` | 1 | 22.07 | 3402664 | 31 | 4 |
| 830 | `19b7689937b54452155bc9b7f9c600e89e224f4fb0a240191c6c400f037a451e` | 0 | 14.22 | 3434532 | 31 | 5 |
| 831 | `19b7689937b54452155bc9b7f9c600e89e224f4fb0a240191c6c400f037a451e` | 0 | 13.82 | 3436168 | 31 | 5 |

825 was green with29 explicit audits; the two new selector helpers still
needed their own print commands. 827/828 were green with31 audits but were
superseded during warning cleanup. Their evidence does not certify the
subsequently edited829 source. 830 was the coordinator's repaired green
source with31 audits and five unused-argument warnings. The attempted830→831
text edit did not match a line-ending form, so831 accidentally repeated the
unchanged successful focused file; it supplies no distinct source evidence.
The coordinator then asserted an actual before/after hash change, removed
only the five flagged arguments, and obtained warning-free832. No unchanged
failed attempt was rerun, no package/full regression was started, and no
limit was raised. 898/899 are the user-reserved independent coordinator
checks, not new development retries.

Intermediate green817 (Digest,8.55s,3382212KiB,swap0) was superseded by819
after removing two unused-variable/tactic warnings. No failed compilation was
rerun unchanged. Failed compiler-generated error terms were not accepted as
proofs.

### Source-region SHA-256

Hashes cover the exact inclusive source lines with original line endings at
the inspection pin; the empty-root table was independently compared in full
with the Rust source by the lead.

| Source | Lines / region | SHA-256 |
|---|---|---|
| T | 156–164 sum_high | `621e9f8efb577377e5e38ed71a401a26c5124f7f16c23f509174b9a2f471d24a` |
| T | 175–178 empty_root | `0e2d77b6fb4bd25e7d1ba8f203af29ef280f2e2ac4b6497c8dd41c14ecb7ca25` |
| T | 218–334 initial/absorption | `9ea397f3abc4b9fcfaee64fc499c9aedd8ccc0f4246190fc5aa78e0b947efc6a` |
| T | 362–391 add_digest_binding / schedule caller | `aa425a44b13eef1160932f4f68708811dd399fd6efab003cfda2cb8162a83570` |
| T | 394–427 literal path | `464faa35b333a280210ceb70be141acffdb8913e9b6dd70b591a98d92c6a5fb0` |
| T | 609–694 public digest accumulator | `b312a79ceb4cd4468d24655891e8a2a8ad0dc43ed79f89685019f8b6cd032054` |
| C | 138–177 high/low selector layout | `06f7aa6e8e482817818250154eb5a7024262f87a3bc1c7938c54838a1d8168ee` |
| E | 2–24 all21 empty-root rows | `3c1f74daf4ee9847948c2ae0f1559af1efa8506a8b0e90ee4b298a168d335b52` |
| poseidon2.rs | 465 tweak | `2c2adc7778bb03513bc2ec9a345df83fd3fc176e582c97edf2deed0c74f8f070` |
| spend.rs | 14–16 domain constants | `c97a9c8dcca562266fb18cfcf96b9eb4a1dcd3334d04237b363e60e1acbe9159` |
| aspis-core/src/field.rs | 55–59 M31.add | `a51f7929c9d6db66d1596dd2a49bad1cfbfafbf1f3d2f84e5cee6e33d212e8d5` |

## Lead decisions after G3/G4 (2026-10-08)

`lean/R0P/CoreExt.lean` (attempt 606, exit 0, `pack4_eq_zero_iff`: propext,
Classical.choice, Quot.sound). `Core.lean` is unchanged, so G1/G2 are unaffected.

- **G4 (Copy):** families that read H1 and λ, χ use `CFamily`/`CHolds`
  (`A 26 b` is H1 at the current row; λ, χ are explicit parameters).
- **G3 (Poseidon), option (a):** the relation is the *unpacked* canonical
  permutation per base limb (P:137–352). `pack4_eq_zero_iff` gives packed = 0 ⇔
  every limb = 0 on base-typed cells under `PackBasis`; `BaseTyped` comes from
  Q11 subfield descent. **That the projected raw-limb code (S:130–357, 401–617)
  computes the canonical permutation is a Rust-to-model refinement obligation,
  recorded here and not proved in this job.**
