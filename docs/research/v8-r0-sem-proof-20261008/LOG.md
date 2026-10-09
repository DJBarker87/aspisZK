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

### Continuation G3″ — complete canonical transition port

Resumed after fetch/fast-forward at lead decision
`1814662d1f51467a7493b573d6d7678819cd0887`. The corrected statement is
implemented without changing Core, CoreExt, constant files or other groups.
Concurrent lead commits `d207e848f` and `99790ae53` added positivity/LogUp
material during this work; their tracked additions are preserved. The
Poseidon imports and reviewed Rust sources are unchanged by those commits.
Every preexisting Poseidon definition and theorem body, including
`poseidonLeadingPair`, `poseidonAbsorbedInput`, `poseidonRoundPair`,
`poseidonRoundKind`, `poseidonBlockRow`, all round functions and
`poseidon_endpoints_do_not_imply_successor`, is preserved byte-for-byte.

**Proved deliverables:**

- `poseidonScalarFamily` emits sixteen unpacked canonical residual lanes.
  It retains T:211–216's ordered block selector over 0..57, S:589–615's
  leading/full/internal selector sums, the three weighted successor
  differences, and the outer block factor. Local row zero uses the existing
  leading pair with the xor12 opening (S:389–398); the other selected rows
  use the canonical interpolated full/internal pairs (S:416–535).
- `poseidon_scalar_holds_iff pub A` is exactly the complete catalogue:
  every block in Fin 57, local transition row in Fin 11 and word in Fin 16
  satisfies its successor equation. `poseidonTransition` reads the existing
  round-pair numbers and dispatches the same initial/internal/final ranges
  as `poseidonRoundKind` (P:239–253,294–308). It selects `poseidonLeadingPair`
  at row zero. The Boolean-row proof identifies xor12 with local row 12,
  successor with local row r+1, and all inactive scalar lanes with zero.
  No off-domain equivalence of arbitrary high/low selector inputs is claimed.
- `poseidon_scalar_holds_output pub A` proves, forward only, that every
  block's local row 11 state equals `poseidonPermutation` applied to
  `poseidonAbsorbedInput`. Generic fold lemmas split the 4+14+4 schedule,
  group all 22 rounds into consecutive pairs, and compose the eleven
  transition equations. The leading external layer and low-eight-word
  absorption are accounted for before the first pair. No permutation value
  or constant table is evaluated.
- `poseidon_packed_iff_scalar F B pub A hA` proves
  `Holds (poseidonPackedFamily B) pub A ↔ Holds poseidonScalarFamily pub A`
  under exactly `B : PackBasis F` and `hA : BaseTyped F A`. The packed
  family groups consecutive scalar limbs as 4*group+limb (T:1253–1255,
  S:600–615) and uses `pack4_eq_zero_iff`. All scalar residuals are proved
  to lie in F, including inactive zeros; no extra relation/extraction
  premise is introduced.

The subfield proof traverses only vector constructors with generic predicate
lemmas and discharges each literal cast with `natCast_mem`. No table index
or numeral value is evaluated. Shift-derived diagonal membership uses the
entire opaque Nat shift expression as a cast. Round and table functions
remain locally irreducible during selector simplification. Only the eleven
local-row cases and seven local selector terms are normalized; neither the
57-block range, 1024-row range nor a concrete finite universe is evaluated.

**Stopped:** none within G3″'s corrected scope. **Findings:** no new source
mismatch. The lead's existing Rust-to-model refinement obligation for the
optimized raw-limb implementation S:130–357,401–617 remains explicit.
The field-level packed residual is the specifically authorized substitution;
this job does not prove that Rust refinement, a converse endpoint theorem,
bijectivity over arbitrary fields, or an extraction/security result.

The coordinator reviewed the literal selected successor branches, block and
lane layout, absorption, interpolation indices and round schedule against
inspection pin `e4d68a70d3f6beb215c9f6dd418f4a2a3740c809`. P, S, T and F
are byte-identical at the lead revision; prior source-region hashes remain
valid. Whole-source SHA-256s for this review:

| Source | SHA-256 |
|---|---|
| P | `3f1d60cf5feb48e56fa3c9379a74f2ccb9b2a7ea78365abf0e06e36e562d54cb` |
| S | `4467d15c9d473cbd42caf33f21aa0192bed007b58ccaa4a61cb5691532cab7fe` |
| T | `efbc5be87e271419d7b09e1bb6e3a83984d42795bc20067ea039814fb89ffa58` |
| F | `5795495e2fa9ad85e097c2ad96ffc826aaad3c16afc0e0bd00459f9f51068cd8` |

Final `Poseidon.lean` SHA-256:
`faeeefd8f3a6c25e1896eb827d9bd12d9bda901ff0171675186064baa5c369c8`.
All focused runs used `dombarker@100.108.41.90`, workspace
`/home/dombarker/project-offloads/aspis-fs-generic-20261006/`, pinned Lean
4.32.0 and its existing objects2/R0P cache, with
`run2.sh N R0P/Poseidon 7000 7`. Each scope used MemoryHigh=5G,
MemoryMax=7G, MemorySwapMax=0, TasksMax=128, timeout 900 s and
`-j1 -M7000 -DElab.async=false`. Reservation admitted 24+7 GiB below 55.
One G3 job ran at a time. No cap changes, local builds, dependency rebuilds
or unchanged failing reruns occurred.

| Attempt | Scope/Lean exit | Wall s | Peak RSS KiB | Swaps | Result/change before next attempt |
|---:|---:|---:|---:|---:|---|
| 906 | 1 | 05.91 | 3381808 | 0 | Selector Fin numerals and inactive simplification; added explicit projection facts. |
| 907 | 1 | 06.28 | 3381528 | 0 | Row-zero Fin equality, xor arithmetic/casts, list quantifier proof and layout syntax; corrected. |
| 908 | 1 | 06.36 | 3381736 | 0 | Remaining row-zero Fin 9/10 comparisons; supplied tiny selector inequality facts. |
| 909 | 0 | 06.48 | 3387736 | 0 | Complete scalar catalogue green, 15 audits; forward composition added next. |
| 910 | 1 | 06.65 | 3383912 | 0 | Generic fold casts, dependent conditionals and lambda inference; corrected explicitly. |
| 911 | 1 | 06.63 | 3383492 | 0 | Final-round Fin projection needed explicit Nat arithmetic. |
| 912 | 1 | 07.38 | 3381956 | 0 | Subfield cast lemma namespace, opacity and introduced lane binders; corrected; forward proof elaborated. |
| 913 | 1 | 07.47 | 3383852 | 0 | Nested-vector predicate needed explicit instantiation for the two external tables. |
| 914 | 0 | 09.22 | 3423824 | 0 | Complete four-deliverable file green, 39 audits, no warnings. |
| 915 | 0 | 09.17 | 3423984 | 0 | Final frozen coordinator check after header update, 39 audits, no warnings. |

Attempt source SHA-256s (915 uses the final hash above):

| Attempt | SHA-256 |
|---:|---|
| 906 | `60f65dffca05ec7cb9f99375c7925ba4659f05304621fba42d28053aabe7b17d` |
| 907 | `05702dad779c5f78ad14af9c636997f0044bcd2864861cdeda448ca917b67c41` |
| 908 | `587e3cd2d1898567277c1c0b90d95b074d642be6581a13ca1301d16925d74a8e` |
| 909 | `e38e5ee37da60e63c6a00760acd4c9ee36c6dbd8adccf25570d3ba94ae138b5c` |
| 910 | `9d84e58efaf71cad4075ce89f86345139cd29aec3f6102b2d6fb5f037f5f3300` |
| 911 | `f0b739e1fc65072436e350bd01f35cdac8c0617f5819559bf1b3c29197fb4c4e` |
| 912 | `18017846d8afb438c3e42638be78384f02562d46e12cf4c1875037765a3467d1` |
| 913 | `b08c0d50cd721023f55db9ac99e414da606f1ed9e10c5980f4879bdad295cf9b` |
| 914 | `250f906979dc5618ad92da801d4ab373fc5c4f79e6b6ded13f428b3a12df567c` |

Raw evidence is `evidence/out-N.log`, `time-N.log`, `sha-N.txt` and
`source-N.lean` in that host workspace for every attempt 906–915. The actual
scope/Lean exit and `/usr/bin/time` exit were inspected; outer runner shell
success was not used to classify a Lean failure. Failed elaborations were
not consumed as proof evidence. The complete development pass 914 and
frozen coordinator pass 915 have zero warnings, errors and swaps.

All 39 theorem declarations (including every private helper) have distinct
`#print axioms` commands. Every audit in 914/915 uses only subsets of
`propext`, `Classical.choice`, `Quot.sound`; `poseidon_vec_nil` uses none.
The new public catalogue, forward-output and packing theorems each use all
three permitted axioms. No forbidden proof term or resource override is
present. Source review, mechanical preservation/audit checks and
`git diff --check` passed. Unrelated untracked work was preserved.

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

## Lead decision after G3′ (endpoint iff)

`poseidon_endpoints_do_not_imply_successor` (f90a42327) is accepted. The
requested G3′ statement was wrong as posed by the lead: a transition family
over a committed trace constrains every local row 0–10, so it cannot be
equivalent to the 57 endpoint equations alone. No Core/CoreExt change.

Corrected statements for G3″ (statement change only; definitions from
f90a42327 are kept):

1. `poseidon_scalar_holds_iff`: `Holds poseidonScalarFamily pub A` ↔
   the complete transition catalogue: for every block and local row
   r ∈ 0..10, the state at local row r+1 equals the row's round pair
   (`poseidonLeadingPair` at r = 0 with the row-12 absorption; the
   `poseidonRoundPair` kinds from `poseidon_round_pair_layout` otherwise)
   applied to the state at local row r.
2. `poseidon_scalar_holds_output` (forward only): `Holds` →
   ∀ block, state at local row 11 = `poseidonPermutation
   (poseidonAbsorbedInput A block)`. Proved by composing the 11 transition
   equations; the permutation and constant tables stay opaque.
3. `poseidon_packed_iff_scalar` as before, against statement 1.

The forward corollary is what the nullifier/membership extraction consumes;
the iff is the literal-port obligation. G4′ (9bdd242f4) is accepted as
complete for its scope.

## Lead: positivity reduced to copy balance (PositivityChain.lean)

`CopyLinkBalance A := ∀ link ∈ copyLinks, producer tuple = consumer tuple`
is the deterministic content of the LogUp argument. `positivity_of_balance`
derives integer positivity from `Holds valueFamily`, `Holds positiveFamily`
and `CopyLinkBalance`; the four cell equalities come from
`copy_positivity_links` at tuple index 0. The sole remaining hypothesis on
this chain is the probabilistic step `CHolds copyFamily lam chi A ⇒
CopyLinkBalance A` (random λ, χ), which is not claimed here.

Attempt 607, `run2.sh 607 R0P/PositivityChain 7000 7`, exit 0, 1.40 s,
3319408 KiB, swap 0, reservation 24+7 GiB. SHA-256 `b45ab3872fa710e44b24119d5d0db24d3aeec41de8791965d4f2cea1d45590f2`.
Axioms: copy_balance_cell, positivity_copy_cells [propext, Quot.sound];
positivity_of_balance [propext, Classical.choice, Quot.sound].

### PositivityChain: weighted balance (attempt 608)

`CopyLinkBalance pub A` now quantifies only over links with
`copyLinkWeight link pub.nextPairIndex pub.variant ≠ 0`; weight-zero links
impose nothing (T:359–377), so the unweighted form was stronger than LogUp
delivers. The four positivity links have weight 1 for every variant/index
(`copy_positivity_links`). Attempt 608, exit 0, 1.38 s, 3319404 KiB,
swap 0, 24+7 GiB. SHA-256 `480aaa1f5393862e55becb598566f85fe54ab6116f729ba11c1f5918440b481c`. Axioms unchanged (standard three).

## Lead: LogUp step design (copy balance from CHolds)

Source: `crates/aspis-statement/src/logup.rs:191–273` (row identity and
global zero sum) and T:1307–1308 (μ batching of `Σ_b H1(b)` and
`Σ_{inactive} H1(b)` into the sumcheck target). χ, λ, μ ∈ QM31,
|QM31| = (2^31−1)^4.

Registry facts (text-checked by the lead on C:27–164, to be proved in Lean
as G5): 136 links; tags are exactly 1124073472 + index (Nodup); no
`(row, slot)` carries two producer endpoints or two consumer endpoints.
Hence on each active row every slot value in `copy_holds_iff` is a single
compressed value `tag + Σ_j λ^{j+1} tuple_j` with the link's weight, or an
absent endpoint with weight 0.

Chain (per fixed committed trace A, variant/index fixed by pub):

1. μ: the sumcheck target is `comp + μ·S₁ + μ²·S₂` with S₁ = Σ_b H1(b),
   S₂ = Σ_{inactive} H1(b). An accepted zero target with S₁ ≠ 0 or S₂ ≠ 0
   needs μ to be a root of a nonzero degree-≤2 polynomial: Pr ≤ 2/|QM31|.
   Deterministic content: S₁ = 0 ∧ S₂ = 0 ⇒ Σ_{active} H1(b) = 0.
2. χ poles: Pr[χ ∈ {all enabled compressed values}] ≤ 272/|QM31|
   (≤ 2 producers + 2 consumers on ≤ 68 active rows is an upper bound;
   the exact count is the number of enabled endpoints).
3. χ off poles: the row identity `Dp(H1·Dc+Nc) = Dc·Np` gives
   H1(b) = Σ_p w/(χ−v) − Σ_c w/(χ−v), so Σ_{active} H1 = 0 is the value at
   χ of the signed rational function F(X) = Σ_enabled ±w/(X−v). With D the
   distinct enabled values and m_v the signed weight at v, F = N'/Π(X−u),
   N'(X) = Σ_{v∈D} m_v Π_{u∈D∖v}(X−u). If some m_v ≠ 0 then N' ≠ 0 of
   degree ≤ |D|−1, so Pr[N'(χ)=0] ≤ 271/|QM31|. Else m_v = 0 ∀v
   (aggregated balance).
4. λ collisions: the ≤ 272 enabled endpoint polynomials
   c_e(λ) = tag_e + Σ_j λ^{j+1} t_{e,j} have degree ≤ 16; distinct
   (tag, tuple) pairs collide at λ with Pr ≤ 16·C(272,2)/|QM31|. Off that
   event, aggregated balance at value c_p(λ) for an enabled link ℓ with
   distinct tags forces w_ℓ·[c_c = c_p] = w_ℓ, i.e. tuple equality, which
   is `CopyLinkBalance pub A`.

Total: ≤ (2 + 272 + 271 + 16·36856)/|QM31| ≈ 2^{19.2}/2^{124}. This is the
bad-set mass for the (λ, χ, μ) rounds; it enters the FS state function as
the per-challenge bad sets of SEM, alongside the existing 397030/(p⁴−1)
ledger. Lead-only; not yet in Lean.

Deterministic Lean obligations (delegable, statements fixed by the lead):

- G5 (registry): `copyLinks.map CopyLink.tag` Nodup via the base+index
  form; per-side (row, slot) uniqueness; enabled-endpoint count bound.
- G6 (partial fractions, Mathlib Polynomial): for a Finset D ⊆ K and
  m : K → K, with N' as above: (a) N' = 0 → ∀ v ∈ D, m v = 0;
  (b) N' ≠ 0 → N'.natDegree ≤ D.card − 1, so roots ≤ D.card − 1;
  (c) for χ ∉ D, Σ_{v∈D} m v / (χ − v) = N'.eval χ / Π_{u∈D}(χ − u).
- G7 (λ compression): for two tagged tuples (t,a), (t',b) ∈ K × (Fin 16 → K),
  the difference polynomial in λ is zero iff (t,a) = (t',b); its degree
  ≤ 16.

## Lead: input-note semantic model and extraction obligation (Semantics.lean)

G3″ (50c7201b5) accepted; `poseidon_scalar_holds_output` is the interface.

Wiring, read from C:27–164 with pair_forest_trace.rs:121–195,
pair_forest_hiding.rs:38–72, poseidon2.rs:464–465,511–529 and
spend.rs:14–16,146–167 (all column indices are C1 columns 0–15; the ports'
`Fin.castAdd` does not shift):

- owner key: block 0, domain 0x4153_0001 length 8, absorbs sk = (0,12) lanes
  0–7; output (0,11) lanes 0–7 → (1,12) (link 7).
- commitment: blocks 1–3, domain 0x4153_0003 length 18, chunks
  pk ‖ (value, asset, salt 0–5) ‖ (salt 6–7); value = (2,12) lane 0 = (63,0)
  lane 10 (link 11), asset = A 1 44 (`asset_holds_iff`); output (3,11) →
  leaf (57,1) cols 1–8 (link 64).
- nullifier: blocks 25–26, domain 0x4153_0002 length 16, chunks sk (link 8)
  ‖ salt (links 9, 10); output row 427 = pub.nullifier (`digest_holds_iff`).
- membership: 24 levels; level k path row 16·(57+k/4)+1+4·(k%4), bit at
  col 0, current cols 1–8, left/right at row+1 cols 0–7/8–15; node block
  4+k (k<21) or 54+(k−21); node = permutation of (left ‖ right) with lane 15
  = right 7 − 1051521018 (= right 7 + 0x4153_1005 in M31; registry offset
  C:21 and MERKLE_NODE_COMPRESSION_V3_TWEAK agree); root (56,11) = anchor.

`Semantics.lean` defines spongeInit/absorb/spongeStep/digestOf, ownerKey,
nullifierHash, noteCommitment, nodeCompress, merkleStep/merkleRoot, the
obligation `InputNoteExtracted pub A` and the trace witnesses traceSk,
traceSalt, pathBaseRow, nodeBlock, tracePath, with `pathBaseRow_mem` and
`nodeBlock_node`. Attempts 609–612 were elaboration fixes (chunk bound
hypothesis, missing Schedule/Digest imports, noncomputable classical bit,
Fin.val reduction); 613 exit 0, 1.66 s, 3341880 KiB, swap 0, 24+7 GiB.
SHA-256 `9309c5faa3de30d4f35bfe46509fe335a821d89a43051201a97232c0b89dc615`. Axioms: standard three.

Next: G8 proves the named link cell equalities from `CopyLinkBalance`
(links 0–2, 7–11, 64–135, in the style of `copy_positivity_links`); G9
proves `InputNoteExtracted pub A` from Holds of schedule, path, digest,
asset, poseidonScalar and `CopyLinkBalance pub A`, via the per-block
lemmas: owner block, three commitment blocks, two nullifier blocks, and the
24-level induction on `merkleRootAux`.

## Lead: pair-forest SEM ledger (SemLedger.lean)

Challenge timing (aspis-prover/src/state_only_candidate_prefix.rs:503–548,
same driver shape for pair forest): trace commitment → λ, χ → H1 commitment
→ θ, μ, zerocheck point → 10 sumcheck rounds (degree 27,
POOL_V1_PAIR_FOREST_MASKED_TERMINAL_DEGREE_V1) → point claims → opening
layer (γ, κ, τ, α, q22). The opening layer selects the trace from
`Lambda W` (`R0.ListsResponses.Lambda_card`: ≤ 100 candidates), after
every semantic challenge, so each semantic branch's bad set is unioned over
candidates: factor 100, as in V7K15 `fixedFamilyCausalRootCap`.

The LogUp λ branch is sharpened from the earlier pairwise-collision count
(16·C(272,2)) to the V7 argument: compression is injective on tagged tuples
as polynomials in λ (G7), so if the enabled producer and consumer tuple
multisets differ, Π(X − c_p(λ)) − Π(X − c_c(λ)) is a nonzero element of
K[λ][X] with some coefficient of λ-degree ≤ 16·136; bad λ ≤ 2176.

| Branch | single trace | ×100 | obligation |
|---|---:|---:|---|
| tupleCompression (λ) | 2176 | 217600 | G7 + unique factorisation lemma (G10a) |
| activePole (χ) | 272 | 27200 | G5 endpoint count |
| copyChi (χ) | 271 | 27100 | G6(b) |
| muBatch (μ) | 2 | 200 | univariate degree 2 |
| thetaLane (θ) | 28 | 2800 | univariate degree 28 (G10b) |
| zerocheckPoint | 10 | 1000 | Mathlib SchwartzZippel, 10 vars (G10c) |
| sumcheckRounds | 270 | 27000 | 10 × degree 27 (G10d) |
| total | 3029 | 302900 | |

302900/(P⁴−1) ≤ 2⁻¹⁰⁵ (`causal_le_two_pow_neg_105`), and 302900 ≤ 396430 so
the V7 reporting figures cover this circuit. Attempt 614,
`run2.sh 614 R0P/SemLedger 7000 7`, exit 0, 1.40 s, 3327444 KiB, swap 0,
24+7 GiB. SHA-256 `21b0896f52defd0d7115a5a2075d85e9bc4405060719596522e6d036f92b1084`. Axioms: standard three or fewer.

Composition target (lead, next): for a fixed candidate t with the opened
claims, semantic acceptance at (λ, χ, θ, μ, zc, α₁..α₁₀) outside the
ledger's bad sets implies `Holds f pub t` for every family f and
`CHolds copyFamily λ χ t`, hence `CopyLinkBalance pub t`, hence
`positivity_of_balance` and (after G9) `InputNoteExtracted pub t`. The
Mathlib `Mathlib.Algebra.MvPolynomial.SchwartzZippel` module is present
in the pinned workspace for the zerocheck branch.

## G5: Copy registry structure

`CopyRegistry.lean` imports `R0P.Copy` and proves the registry facts needed by the deterministic LogUp obligations. It retains the literal three-block registry structure: 14 entries before the positivity block, 4 positivity entries, and 118 entries after it. The tag theorem is assembled from separately proved block equations and a symbolic range-concatenation lemma; the full `copyLinks` list is never passed to `decide`. The producer and consumer `(row, slot)` facts use block-local nodup checks and finite cross-block disjointness checks, then generic list lemmas. A generic slot-cardinality lemma maps a row-filtered nodup list into `Fin 2`; the enabled-row bounds follow by filtering by endpoint row and nonzero weight, and the public/index-wide enabled-link bound follows from the 136-entry length.

The lead's independent source review compared all 136 ordered records and all nine fields against Rust `COPY_LINKS` at C:27–164. It found the blocks 14+4+118, tags `1124073472 + index` through `1124073607`, 136 distinct producer keys and 136 distinct consumer keys, and at most two endpoints per row on either side. Review input: `/tmp/r0-logup-20261008/registry-source-review.json`; the text-parse comparison took 0.00133 s locally. This is source-review evidence, not Lean proof evidence. Rust pin: `e4d68a70d3f6beb215c9f6dd418f4a2a3740c809`. Worktree began at `50c7201b5`; the lead advanced shared HEAD during this work (current HEAD at freeze and final check `1074cbc4915fcd36dbfeee3b45c88808d7cc5770`). The exact Lean source SHA is recorded per run below.

Attempts ran sequentially on `dombarker@100.108.41.90`, workspace `/home/dombarker/project-offloads/aspis-fs-generic-20261006/`, with `run2.sh <attempt> R0P/CopyRegistry 7000 7`; every reservation check reported 24 GiB populated + 7 GiB for this scope. Pinned Lean was 4.32.0 with the existing object cache; no package or dependency rebuild was started. Scope settings were `MemoryHigh=5G`, `MemoryMax=7G`, `MemorySwapMax=0`. All swaps were zero. Failures were proof/elaboration defects corrected in later changed sources, not source obstructions. The 34 axiom-audit commands on successful attempt 1103 reported only `propext`, `Classical.choice`, and `Quot.sound`; no warnings were emitted.

| Attempt | Source SHA-256 | Lean exit | Wall | Peak RSS (KiB) | Swap | Axiom audit lines | Warnings | Finding |
|---|---|---:|---:|---:|---:|---:|---:|---|
| 1100 | `10a9060deb0829059e65ef48ed606c92645b6b0399a4e7cbfafe4b53be18a22c` | 1 | 6.77 s | 3,624,208 | 0 | 28 | 0 | Initial generic filter/cardinality facts used Prop predicates with `List.filter`'s Bool interface; block disjointness lacked a finite-check bridge; range/tag composition was incomplete. |
| 1101 | `2d6b87c9f609de04f1043b44ce8d5b85035da794ccca8311b690ac7539fcbfd0` | 1 | 8.03 s | 3,620,116 | 0 | 31 | 0 | Bool-filter conversion and finite disjointness approach were corrected; remaining issues were disjointness statement shape, range/map associativity, and classical decidability in theorem result filters. |
| 1102 | `969e8e039f64d1d9ec6be2055d691e998139714fdebfd5216226bf2aa92b3df1` | 1 | 7.86 s | 3,620,336 | 0 | 34 | 0 | Only the range append helper's rewrite sequence remained open; tag theorem inherited that helper. |
| 1103 | `42a78275bbe6dccebc1a7843e7260b2591c25ed5add271c79e1db99d4e820906` | 0 | 7.83 s | 3,619,856 | 0 | 34 | 0 | Green and frozen source; all requested registry statements compile and all axioms are permitted. |
| 1198 | `42a78275bbe6dccebc1a7843e7260b2591c25ed5add271c79e1db99d4e820906` | 0 | 7.84 s | 3,620,576 | 0 | 34 | 0 | Coordinator focused check of the frozen source; actual scope and time exits both zero. |

On green 1103 the public declarations are `copy_tags_indexed`, `copy_tags_nodup`, `copy_producer_slots_nodup`, `copy_consumer_slots_nodup`, `copy_enabled_endpoints_le`, `copy_active_row_producers_le`, and `copy_active_row_consumers_le`. The per-row theorems retain the required `CopyActiveRow b` premise and quantify over every `pub`; their filters require the corresponding endpoint row and nonzero `copyLinkWeight`. The structural record evaluation is limited to the three registry blocks (136 records total); the generic row bound uses only symbolic `Fin 2` cardinality, with no 1024-row or large-universe normalization. No `sorry`, `axiom`, `admit`, `native_decide`, `maxRecDepth`, or `maxHeartbeats` is used.

The coordinator reviewed the complete final source and independently read the raw attempt records. Failed attempts 1100–1102 contain compiler error-term axioms and are rejected as proof evidence. Every theorem (30), including private helpers, is audited; the four additional audits cover helper definitions. Actual scope and time exits agree for all five runs. Rust C whole-file SHA-256: `cfce7ec499d3cfd54cf91eb88675e45d89ada5ce073fe00c78be5211204fbc50`; C:27–164 SHA-256: `46187e7618fcba23fabf27f20e7f892ca5e4df38ab619ad84f238bf10ffc4e71`.

Raw artifacts are `evidence/source-{1100..1103}.lean`, `evidence/sha-{1100..1103}.txt`, `evidence/out-{1100..1103}.log`, and `evidence/time-{1100..1103}.log` in the pinned build workspace. Final worktree/build-host source SHA matches `42a78275bbe6dccebc1a7843e7260b2591c25ed5add271c79e1db99d4e820906`. No Lean job or build scope remained active after 1103. Coordinator check 1198 then passed with the same source hash and reservation 24+7 GiB. Its `source-1198.lean`, `sha-1198.txt`, `out-1198.log`, and `time-1198.log` are retained under `evidence/`. No source obstruction or probability claim is recorded.

## G6: LogUp partial fractions

- Target: `R0P/LogUpFrac`, tested on host `dombarker@100.108.41.90` (`nuc`), workspace `/home/dombarker/project-offloads/aspis-fs-generic-20261006`.
- Pinned Lean: `leanprover/lean4:v4.32.0` (`LEAN_GITHASH=8c9756b28d64dab099da31a4c09229a9e6a2ef35`). `evidence/run.py` invokes Lean with `-j1 -M4500 -DElab.async=false`; `run.sh` scopes the run at `MemoryHigh=5G`, `MemoryMax=7G`, `MemorySwapMax=0`, `TasksMax=128`, timeout 900 s. `run.sh` SHA-256: `0fdf22312034806a22f95ae2f30583c9fc5ea63b142cd98cee76f79fcfbc348b`.
- Reservation before final run: populated capped reservation 24 GiB, thus 24+7=31 GiB ≤ 55 GiB. Development attempt 1220: runner/scope exit 0; `/usr/bin/time` exit 0; 1.22 s wall; peak RSS 2,087,128 KiB; swap 0. No host cap was changed.
- Source HEAD during final check: `1074cbc4915fcd36dbfeee3b45c88808d7cc5770`; final source SHA-256 `f4d1c635188c74aeb5e2150e94b8627c22439e0bf1a482a173c0a5b38566b0b2`.
- Raw evidence: host `evidence/source-N.lean`, `evidence/sha-N.txt`, `evidence/out-N.log`, `evidence/time-N.log`, for all run IDs below, including final coordinator check 1298.
- Rust source context from lead, inspection pin `e4d68a70d3f6beb215c9f6dd418f4a2a3740c809`: `logup.rs` whole-file SHA-256 `c6e84617e6473f014fc53c704dd26b04667046211985ea6ddca8f66f496bea65`. Its lines 191–273 SHA-256 `14ff810b91e426ff0974134f8be73eddebb85eb52f3d4581b441b24e193da661`. The proved `numer` is the lead-specified polynomial model; it is not asserted as a direct definition of Rust `logup.rs`.
- Audits: all 8 theorem/private-helper `#print axioms` checks in final output contain only `[propext, Classical.choice, Quot.sound]`; no warnings in attempt 1220.

The file defines `numer D m` as the specified finite sum of `C (m v)` times the erased-support polynomial product. It proves numerator vanishing implies every coefficient on `D` vanishes; the requested public nonzero theorem gives both the natDegree and multiplicity-counted roots bounds; and `numer_partial_fraction` assumes only `chi ∉ D`. There is no nonemptiness premise and no table/range evaluation.

### Attempt inventory and final check

IDs 1200–1206 have no G6 runner artifacts (`sha/out/time`) in the host evidence directory; the lead's initial check confirmed 1200 was unused before this work, so these IDs were not run for G6. IDs 1207–1220 below are every G6 development attempt; 1298 is the coordinator check. “Runner” is the outer status appended by `run.sh`; “time” is `/usr/bin/time`'s `Exit status` (the inner command result). Every run used the fixed scope above and reported zero swap.

| ID | Source SHA-256 | Runner | time | Wall | Peak RSS KiB | Swap | Finding |
|---:|---|---:|---:|---:|---:|---:|---|
| 1200 | not run; no artifact | — | — | — | — | — | Confirmed unused before work. |
| 1201 | not run; no artifact | — | — | — | — | — | No G6 run. |
| 1202 | not run; no artifact | — | — | — | — | — | No G6 run. |
| 1203 | not run; no artifact | — | — | — | — | — | No G6 run. |
| 1204 | not run; no artifact | — | — | — | — | — | No G6 run. |
| 1205 | not run; no artifact | — | — | — | — | — | No G6 run. |
| 1206 | not run; no artifact | — | — | — | — | — | No G6 run. |
| 1207 | `21cf3c2800dabdbc2e69406f17b6ed044c9e098ce7b30b44da2324542fa1e1a9` | 134 | 0, signal 6 | 2.99 s | 6,152,596 | 0 | `import Mathlib` triggered Lean interpreter `memory_exception`; changed imports, no cap increase. |
| 1208 | `3e3e869205a19645f518af2fcc92732082040c650d8ac6642ddae8c3ed15c6bd` | 1 | 1 | 1.52 s | 2,067,392 | 0 | Missing `open Polynomial`; corrected. |
| 1209 | `94a6215da898226482be6e7205c2acbfbc533ccbbd43eb54262acd942a1ce0c6` | 1 | 1 | 1.43 s | 2,069,092 | 0 | Elaboration and degree/root application errors; repaired. |
| 1210 | `8f582dc0f6bb0ac1967c3f09e99478712bf783481f0335872dd1be451dcfff9b` | 1 | 1 | 1.10 s | 2,069,148 | 0 | Classical decidable equality/noncomputable scope and remaining proof errors; repaired. |
| 1211 | `d25a08595adecae08e2bc943ad77b3a99750d643bfa536fbd77bddb9e55a5d25` | 1 | 1 | 1.21 s | 2,077,560 | 0 | Singleton-sum proof shape and product factorization; repaired. |
| 1212 | `96395c9797db93cb3f7e012fd5a1d242790b452a6f683e8d9cd74a3ee2abc70c` | 1 | 1 | 1.21 s | 2,076,616 | 0 | Singleton-sum side-condition order; repaired. |
| 1213 | `fdb4eced2f344a6ad45cc0c077a166a29c37810719178c9e0563e64317bf1931` | 1 | 1 | 1.17 s | 2,076,080 | 0 | Off-term product-zero proof; repaired. |
| 1214 | `db2409328314fc01b5df384b05aa308bd1f1c2c6a7464283871d66baa548b682` | 1 | 1 | 1.20 s | 2,076,812 | 0 | Product-zero target shape; refined. |
| 1215 | `9824b95dfe5dd025e4bcd72cc155f8fa492c45f587620854de6000f5733b1c8f` | 1 | 1 | 1.17 s | 2,076,880 | 0 | Product-zero proof target; refined. |
| 1216 | `d19640d65b367ccf5f186686432b78d7d534d6cae8e254858019f44394061018` | 1 | 1 | 1.16 s | 2,076,280 | 0 | Product-zero proof target; refined. |
| 1217 | `db2409328314fc01b5df384b05aa308bd1f1c2c6a7464283871d66baa548b682` | 1 | 1 | 1.18 s | 2,076,716 | 0 | Product-zero proof target; refined. |
| 1218 | `f6648b94ef0bc51f33a9379e5d75705c3fde6fe6694a659ec75ae93161a51b48` | 1 | 1 | 1.20 s | 2,077,196 | 0 | Confirmed `Finset.prod_eq_zero` requires the vanishing-factor proof. |
| 1219 | `588dae03c8931ac97fcb28adb6d3e88086e0bca928f348f3f16d05a2fecdfe26` | 0 | 0 | 1.23 s | 2,087,648 | 0 | Green; unused-premise warning remained. |
| 1220 | `f4d1c635188c74aeb5e2150e94b8627c22439e0bf1a482a173c0a5b38566b0b2` | 0 | 0 | 1.22 s | 2,087,128 | 0 | Final green; nonzero premise explicitly used, no warnings. |
| 1298 | `f4d1c635188c74aeb5e2150e94b8627c22439e0bf1a482a173c0a5b38566b0b2` | 0 | 0 | 1.20 s | 2,087,160 | 0 | Lead's frozen-source final check; 8 audits, no warnings; reservation 24+7=31≤55 GiB. |

Workflow deviation: attempt 1217 reran exactly the same source SHA and unchanged failing source as attempt 1214 (`db2409328314fc01b5df384b05aa308bd1f1c2c6a7464283871d66baa548b682`). Both logs show the same unsolved `v - v = 0` goal at the same line, with outer/time exits 1/1. This was an accidental repeat while exploring proof-term variants; it violated the no-unchanged-failing-rerun rule. The repeat used the unchanged 5G/7G/0 scope, lasted 1.18 s, peaked at 2,076,716 KiB, and swapped 0. Evidence is retained. No cap was raised. The final frozen-source check is attempt 1298 above. The coordinator reviewed the complete source and raw evidence; all failed compiler error-term audits are rejected. No source obstruction or probability claim is recorded.

## G7

### Tagged compression polynomial

`lean/R0P/LogUpCompress.lean` implements the lead's fixed G7 statements from
"Lead: LogUp step design". Source inspection pin:
`e4d68a70d3f6beb215c9f6dd418f4a2a3740c809`. The development source snapshot is
base revision `26a11aee35691c84da29cf955ea133d6d72eb66e` plus the new file at
the final SHA-256 below. Existing Core, CoreExt, Copy and other groups' files
are unchanged by G7.

The exact definition is
`compressPoly p = C p.1 + sum_j C (p.2 j) * X^(j.val+1)`, with `j : Fin 16`.
The tag therefore occupies coefficient zero, and all sixteen tuple limbs
occupy coefficients one through sixteen. `noncomputable` is required for
Mathlib's polynomial construction over an arbitrary field and changes no
formula or premise.

Proved, over arbitrary `[Field K]`:

- `compressPoly_eq_iff`: two compression polynomials are equal iff their
  complete tagged tuples are equal.
- `compressPoly_sub_eq_zero_iff`: their difference is the zero polynomial
  iff their complete tagged tuples are equal.
- `compressPoly_sub_natDegree_le`: every such difference has natural degree
  at most sixteen, including a zero difference.
- `compressPoly_eval`: evaluation at `lam` equals the tag plus
  `sum_j copyPowers lam j * p.2 j`.

The private coefficient helpers isolate coefficient zero and coefficient
`j.val+1`. The latter uses `Finset.sum_eq_single` and injectivity of the Nat
limb exponent; it does not enumerate the sixteen indices. The private
degree helper uses the generic finite-sum degree bound. Evaluation invokes
the already proved `copy_powers_eq`, then field multiplication commutativity
inside a lemma. No source table, concrete finite universe, or 1024-row range
is evaluated. No fixed-lambda evaluated-value injectivity, probability,
root-counting claim, extraction implication, or copy balance is asserted.

Source correspondence: `crates/aspis-statement/src/logup.rs:75–83` starts
with the lifted tag, initializes the running power to lambda, adds each
power times its tuple limb, then multiplies the power by lambda once.
`pool_v1/pair_forest_copy_terminal.rs:237–244` constructs the same sixteen
powers; `Copy.lean:46–47,367–368` supplies the literal loop and its power
identity. No non-literal construct or additional premise was needed.

| Source | Region | SHA-256 |
|---|---|---|
| `logup.rs` | Whole file; unchanged from inspection pin, independently reviewed by lead | `c6e84617e6473f014fc53c704dd26b04667046211985ea6ddca8f66f496bea65` |
| `logup.rs` | Lines 75–83 | `cc365a8cfca6f12d2ce23aa2690dce1cf86bd2f3be77415a7a7efbcb2981dbbb` |
| `pair_forest_copy_terminal.rs` | Lines 237–244 | `fde6c5814e11fe7c99981145659bd60c5c49c838af792db57731ed14bf81a17b` |

### Build evidence

Host `dombarker@100.108.41.90`, workspace
`/home/dombarker/project-offloads/aspis-fs-generic-20261006/`, pinned Lean
4.32.0 and existing object cache. Every attempt used
`run2.sh N R0P/LogUpCompress 7000 7`: `-j1 -M7000 -DElab.async=false`,
MemoryHigh=5 GiB, MemoryMax=7 GiB, MemorySwapMax=0, TasksMax=128,
timeout=900 seconds. The runner's reservation admitted 24+7 GiB against its
55 GiB ceiling on all development attempts and final check 1398. One G7 job at a time, no cap change,
local compilation, dependency rebuild, or unchanged failed rerun.

| Attempt | SHA-256 | Lean/scope exit | Wall s | Peak RSS KiB | Swaps | Status |
|---:|---|---:|---:|---:|---:|---|
| 1300 | `dd5b387d3429e62c15f65187fa687506e8beda10617ce15dd0743aeb2a390361` | 1 | 2.63 | 6679480 | 0 | Failed: polynomial definition needed `noncomputable`; secondary realization errors and compiler error terms rejected |
| 1301 | `c1fa19babf90e5f5168d9843693c7075611dfd7716fd583cbd44fd34d14a25ad` | 0 | 2.88 | 6720188 | 0 | Green, seven permitted audits, no warnings; superseded by narrow imports |
| 1302 | `2a8ee84dbbc341e899441847ef68ed4f91c1a25d308a2124966bf3c587a32c4e` | 0 | 1.53 | 3323484 | 0 | Frozen development pass, seven permitted audits, no warnings |
| 1398 | `2a8ee84dbbc341e899441847ef68ed4f91c1a25d308a2124966bf3c587a32c4e` | 0 | 1.48 | 3323492 | 0 | Coordinator frozen-source check; seven permitted audits, no warnings |

1301 followed the actual `noncomputable` declaration correction. After the
lead recommended narrower cached imports, 1302 replaced only `import
Mathlib` with `import Mathlib.Algebra.Polynomial.BigOperators`; every
definition, theorem statement and proof is otherwise identical to 1301.
The needed `.olean` was verified present before the import change, and the
peak RSS fell to roughly 3.17 GiB. No failed object was used as proof evidence.

All seven theorem declarations, including the three private helpers, have
explicit `#print axioms` commands. At 1302 every theorem uses exactly
`[propext, Classical.choice, Quot.sound]`. Declaration/audit counts match
without duplicates. Source scanning found no prohibited proof constructs;
the whitespace check emitted no diagnostics.

Raw evidence is `evidence/source-N.lean`, `evidence/sha-N.txt`,
`evidence/out-N.log`, and `evidence/time-N.log` for N=1300,1301,1302,1398. Scope
exit and `/usr/bin/time` exit agree; the outer runner's exit is not used to
classify a Lean failure. Each development attempt also has a local exact source backup
at `/tmp/r0-logup-20261008/LogUpCompress-N.lean`. The final local and remote
source hashes match. Coordinator check 1398 passed after independent source and statement review at shared HEAD `1074cbc4915fcd36dbfeee3b45c88808d7cc5770`; all seven audits use only the three permitted axioms and the scope/time exits both equal zero. No source obstruction was found.

## Lead: sumcheck soundness and zerocheck composition (Sumcheck.lean, Zerocheck.lean)

`Sumcheck.lean`: `bsum` (hypercube sum by recursion on the leading
coordinate), `IndDeg d n G` (every round's honest polynomial exists with
degree ≤ d, for every prefix), `accept d n G c polys α` (boundary check
`p(0)+p(1)` = running claim, degree check, final `G α = claim`), and
`sound`: an accepted false claim makes some `α i` a root of a nonzero
polynomial of degree ≤ d (`polys i − honest i`), by induction on n.
Attempt 615, exit 0, 0.89 s, 1944912 KiB, swap 0. SHA-256 `4d14c4f8e6488e39e0a8c50ada54f6116c489214bc0e0e7c827b4aedab2a599a`.

`Zerocheck.lean`: `ofBool`, `bsumB`, `eqwB` (Boolean eq weight),
`mle` (recursive multilinear extension), with `bsum_eq_bsumB`,
`bsumB_smul`, `bsumB_add`, `bsumB_eqw : Σ_b eq(z,b)·f(b) = mle f z`;
`lanesComp θ lanes b = Σ_{i<29} θ^i lane_i(b)`; the four bad-set
definitions `BadAlpha 27 10`, `BadMu`, `BadZc`, `BadTheta` (ledger
branches sumcheckRounds, muBatch, zerocheckPoint, thetaLane), and
`compose`: if G's Boolean values are
`eq(zc,b)·lanesComp θ lanes b + μ·H1 b + μ²·inact b` (T:1303–1308),
`IndDeg 27 10 G`, the sumcheck accepts claim 0, and α, μ, zc, θ avoid
their bad sets, then every lane vanishes on every row and
`Σ_b H1 b = 0 ∧ Σ_b inact b = 0`. Attempts 616–617 were an import name
and a Fin 0 base case; 618 exit 0, 1.35 s, 1964792 KiB, swap 0, 24+7 GiB.
SHA-256 `6e6b88599348de3f314a074e1396f5034d019ef4210d06a3ecce65a6ff53d14f`. Axioms: standard three.

Remaining for the SEM composition:
1. Bad-set cardinalities on these function-level definitions (re-scoped
   G10): `BadMu` ≤ 2, `BadTheta` ≤ 28 (at a witnessing row the lane
   vector is nonzero, so θ is a root of a nonzero degree-≤28 univariate),
   `BadZc` ≤ 10·|K|^9 by induction on `mle` (DeMillo–Lipton–
   Schwartz–Zippel on the degree-1 leading coordinate), and `BadAlpha` at
   strategy level: with `polys i` a function of `α 0..i−1`, the event
   has mass ≤ 10·27/|K| (the per-round root set is fixed before `α i`).
2. The lane map (G11): `lanes i b` for a trace `t` is the terminal's
   i-th θ-lane at row b: 4 packed Poseidon lanes, 24 packed semantic lanes
   from the 94 source lanes (T:1253–1255, `semantic_packed`), and the copy
   residual; with `pack4_eq_zero_iff` under `BaseTyped` this gives
   `Holds f pub t` for every ported family and `CHolds copyFamily λ χ t`.
3. `IndDeg 27 10 G` for the actual virtual polynomial: the terminal's
   per-variable degree bound (POOL_V1_PAIR_FOREST_SEMANTIC_ZEROCHECK_INDIVIDUAL_DEGREE_V1 = 27);
   and `hG`, that the terminal evaluated at Boolean openings equals the
   batched row value (the three opened points at a Boolean row are the row,
   its successor and its xor-12 row, which is what the ports' `rowOpenings`
   and `rowSel` encode).

## G8: Copy input-note and Merkle path links (`CopyInputLinks.lean`)

`CopyInputLinks.lean` imports the fixed `PositivityChain` and `Semantics` interfaces (with Copy available transitively). It proves the nine input/leaf equalities from `CopyLinkBalance` and proves the per-level path input/output equalities for all 24 levels. The theorem statements add no trace-extraction, relation, or probabilistic premise. `copy_path_cells_of_balance` retains the registry's ordered source/consumer distinction: its right-input equation is

`A (i+8) (succRow (pathBaseRow level)) = A (i+8) (16 * (nodeBlock level).val) + (if i = 7 then 1051521018 else 0)` (column-first notation, with the theorem carrying the explicit Fin bounds).

Thus the only offset is the source-prescribed lane-15 addition on the right endpoint. For levels `< 23`, the path node output is equated to the next path row. The final level has no output link.

The literal registry remains three blocks in `CopyConstants.lean`; this module does not modify those tables. The path accessors select exactly the left, right, and output records at after-block indices `47+3k`, `48+3k`, and `49+3k` for the 23 nonfinal outputs (the last level has only its left/right pair). Each level's field-level record facts are proved by a bounded 24-way split. The proof does not decide the full registry or any trace/range/universe. This bounded case split evaluates only the selected path record fields; the complete focused build took 5.06 seconds.

Source review at Rust pin `e4d68a70d3f6beb215c9f6dd418f4a2a3740c809` independently checked all 80 requested records (input links 0–2, 7–11 and registry links 64–135): all records match and every selected `weight_kind` is 0. The full constants source SHA-256 is `cfce7ec499d3cfd54cf91eb88675e45d89ada5ce073fe00c78be5211204fbc50`; selected region hashes are C:10–25 `049361cce80ce94b016e40afabba2db28e396ee090659609e7880735abd86737`, C:28–39 `39ace0508638f8e9e53d0ae63149bf06d48e0b78fb00aa58607a96321732f74e`, and C:92–163 `1366eb517cfe9e5f5884df83a450c99d8f2827fe0b7ea49991f2bea270391e15`. The independent machine-readable review is `/tmp/r0-extraction-20261008/source-review.json` (0.087 s). The right-input tweak also matches the Rust semantic description at `pair_forest_trace.rs:121–195` and `poseidon2.rs:464–465`; their region hashes are respectively `c55d0915b981008e31ff2caa529d3cf62d82c94055d683276756dc015f9837e6` and `87215a38c95bf136df138d82f492232ae3b792565b7cfccdabac95d5edb092cb`.

Work started at `523cd4af9ca79cd0568932109e26b2d308c6a022`; the lead added concurrent work at `a22519dc846c64f3fb84906b367032b5d47c51a9`, which was preserved. Final focused checks used that revision plus the source hash below. Focused builds ran only on `dombarker@100.108.41.90`, with pinned Lean 4.32.0 and existing cached objects, in `/home/dombarker/project-offloads/aspis-fs-generic-20261006`, using `run2.sh <attempt> R0P/CopyInputLinks 7000 7`. The runner reported a 24 GiB populated reservation plus this 7 GiB scope on every attempt; its scope set `MemoryHigh=5G`, `MemoryMax=7G`, and `MemorySwapMax=0`. Raw stdout and `/usr/bin/time -v` records are `evidence/out-N.log` and `evidence/time-N.log`; source snapshots and SHA records are `evidence/source-N.lean` and `evidence/sha-N.txt`.

| Attempt | Source SHA-256 | Lean/scope exit | Wall | Peak RSS | Swap | `#print axioms` output | Finding |
| --- | --- | ---: | ---: | ---: | ---: | ---: | --- |
| 1400 | `2eaad70e0574ef7bdd6f8c494947f1ac90a6b7fdc592c2c99bcac2af9e987520` | 1 | 3.62 s | 3,362,236 KiB | 0 | 36 | Getter bounds were not reduced to literal block lengths; initial Fin column embeddings and lane-branch proofs did not elaborate. Failed declarations reported `sorryAx`; this was not green evidence. |
| 1401 | `e3ff0aeddfe24a204a36283e74ce1c14cf96fb2567e86295f90becd6800e7e9a` | 1 | 3.71 s | 3,362,600 KiB | 0 | 36 | Getter lengths were made explicit. Remaining failures were nested/incorrect lane projections, including a `Fin 2`/`Fin 16` mismatch and the singleton pattern rewrite. |
| 1402 | `dfe9364b09f24612f2bee0454a1de6250ba4019e9ded118f627719303d842c52` | 1 | 3.78 s | 3,362,776 KiB | 0 | 36 | Corrected lane indices and isolated singleton input, but the pattern-3/5 table rewrites and conditional lanes remained unresolved. |
| 1403 | `56d550d7be2d535749d29e7ac67f80dafa338f16d2b0e09b0b13451bd80d835b` | 1 | 3.70 s | 3,362,396 KiB | 0 | 36 | Dependent `if` branches were not discharged; singleton conditional simplification still had an unresolved proposition. |
| 1404 | `92dab1562eabe16387b2448f5156bf10cf88a26773681c7e3e7ff7245bbcec4f` | 1 | 3.71 s | 3,364,924 KiB | 0 | 36 | Used `dif_pos`/`if_pos` for the wrong side of pattern-2/5 equations; lane conditions remained. |
| 1405 | `a11d782f8dba9924e18b6a9234e88cc0f34cde77281cc0df5c16ec58aed4d011` | 1 | 3.76 s | 3,364,840 KiB | 0 | 36 | Unfolded the local Fin lane index and separated ordinary/dependent conditional rewrites; the two short salt-window goals still had unresolved active-lane conditionals. |
| 1406 | `91ab7a1c83350fe13a78821594df30fe133225fab026a490402d858d164a3ff7` | 0 | 3.88 s | 3,388,248 KiB | 0 | 36 | Partial green: the nine input/leaf link equalities compiled without warnings. The Merkle path bridge had not yet been added; this was not the final module. |
| 1407 | `98df78be7f43175a2a252f0103fa130810df62fc3066ed78c9bf03f50bcc5806` | 1 | 4.43 s | 3,385,556 KiB | 0 | 43 | The added path record specs tried to decide equality of non-`DecidableEq` endpoint structures, and the right-lane bound remained. Replaced structure equality with the individual row/pattern field facts. |
| 1408 | `877b5065296a90a4fd139755057fc28fbc65099d818d0b168737635c98f886ff` | 0 | 5.06 s | 3,415,200 KiB | 0 | 43 | Final full-file green; no Lean warnings. All 43 declaration audits use only `propext`, `Classical.choice`, and `Quot.sound`. No `sorryAx` or other axiom is present. |
| 1498 | `7575812a8719c53c74a7736037a0f109dc34420f69709e0cf41f0de96a84ff95` | 0 | 5.06 s | 3,414,580 KiB | 0 | 43 | Coordinator final pass; no warnings; both public signatures independently printed and reviewed. |

Before final check 1498, the coordinator removed the unused `CopyRegistry` import and added precise provenance/method comments and two `#check` interface commands. The proof statements and proof terms were unchanged. This produced a distinct final source snapshot; no unchanged source was rerun. Final local and build-host SHA-256 is `7575812a8719c53c74a7736037a0f109dc34420f69709e0cf41f0de96a84ff95`. It has 43 named declarations and 43 matching axiom audits, all permitted. All archived attempt snapshots match their SHA records, and scope/time exits agree. No package/dependency rebuild, local Lean compilation, source discrepancy, or cap change occurred.

## G9: Input-note extraction

`lean/R0P/Extraction.lean` proves the lead's exact
`input_note_extracted` theorem. Its assumptions are Holds of Schedule, Path,
Digest, Asset and the canonical scalar Poseidon family, plus
`CopyLinkBalance pub A`; its conclusion is the unchanged
`InputNoteExtracted pub A`. The existential witnesses are exactly
`traceSk A`, `traceSalt A`, and `tracePath A`. No assumption or model
definition was added or weakened. Existing Lean files were not edited by G9.

The proof first turns `poseidon_scalar_holds_output` into a rate-eight
`spongeStep` equation without evaluating the permutation. Schedule supplies
the domain/length states for blocks 0, 1 and 25 and the final note chunk's
zero rate lanes 2–7. G8's fixed links supply continuation states, the owner
chunk, the shared secret key, both salt segments, the value cell and the
commitment-to-leaf connection. Asset supplies `A 1 44 = pub.assetId`.
This proves the owner hash, three-block note commitment and two-block
nullifier for the prescribed cells.

For each symbolic path level, the Path Boolean equation gives either a zero
bit and left=current or a nonzero bit, hence bit=1 and right=current. G8's
left/right links and Schedule's zero rate state identify the node input. The
capacity lane 15 equation moves the registry's `+1051521018` offset to
`right 7 - 1051521018`, exactly the lead's existing `nodeCompress` model.
No characteristic premise or reinterpretation of that model is introduced.
A Nat induction, with the bound `n < 24`, relates `merkleRootAux` to each
successive path-row current digest. The final recurrence step at level 23
ends at node block 56, row 907; Digest binds it to `pub.anchor`. Digest also
binds block 26's output row 427 to `pub.nullifier`.

The permutation and `merkleRootAux` are locally irreducible in the proof.
Only explicit recurrence equations are rewritten: no permutation, constant
table, concrete trace, row range, or concrete finite universe is evaluated.
The induction does not unroll the 24-level path. No source/model discrepancy
was found. Runtime freshness and the separate raw-limb refinement boundary
are not newly claimed by this deterministic theorem.

### Source and dependency records

Rust inspection pin: `e4d68a70d3f6beb215c9f6dd418f4a2a3740c809`.
The worktree began this job at `523cd4af9ca79cd0568932109e26b2d308c6a022`;
the coordinator preserved and fast-forwarded concurrent lead work to
`a22519dc846c64f3fb84906b367032b5d47c51a9`, the shared revision at the final
development check. The exact new source is identified by its final hash.

The immutable `Semantics.lean` model has SHA-256
`9309c5faa3de30d4f35bfe46509fe335a821d89a43051201a97232c0b89dc615`.
The final G8 dependency, checked by the coordinator at 1498, has SHA-256
`7575812a8719c53c74a7736037a0f109dc34420f69709e0cf41f0de96a84ff95`.
The coordinator's source inspection is recorded in
`/tmp/r0-extraction-20261008/source-review.json`: the requested 80 links
match the source and all have weight kind zero, with 24 path levels and 23
interlevel output links. G9 consumes G8's proved cell equalities, not the
text inspection as a premise.

| Source | Inclusive region | SHA-256 |
|---|---|---|
| `poseidon2.rs` | 511–529, sponge trace | `2d043dfeb6d3a630b8fdd904f127bdb4247d8e8f78bf2aa67f14ccecb14f8409` |
| `poseidon2.rs` | 464–465, node tweak | `87215a38c95bf136df138d82f492232ae3b792565b7cfccdabac95d5edb092cb` |
| `spend.rs` | 14–16, domains | `c97a9c8dcca562266fb18cfcf96b9eb4a1dcd3334d04237b363e60e1acbe9159` |
| `spend.rs` | 146–167, note layout | `a628803f938a35464d645a59fd46a7c92df5dd968933be77adb5f2aaa7f29f97` |
| `pair_forest_trace.rs` | 121–195, path/node trace | `c55d0915b981008e31ff2caa529d3cf62d82c94055d683276756dc015f9837e6` |
| `pair_forest_hiding.rs` | 38–74, private path cells | `fce8e1db72056efe46c842b974b12668a73b2d9618c7583da35937417555dc74` |
| `pair_forest_copy_terminal_constants.rs` | 10–25, patterns | `049361cce80ce94b016e40afabba2db28e396ee090659609e7880735abd86737` |
| same | 28–39, fixed input links | `39ace0508638f8e9e53d0ae63149bf06d48e0b78fb00aa58607a96321732f74e` |
| same | 92–163, leaf/path links | `1366eb517cfe9e5f5884df83a450c99d8f2827fe0b7ea49991f2bea270391e15` |

### Build evidence

All attempts targeted `R0P/Extraction` on `dombarker@100.108.41.90`,
workspace `/home/dombarker/project-offloads/aspis-fs-generic-20261006/`,
pinned Lean 4.32.0 and existing cached objects. Commands were
`run2.sh N R0P/Extraction 7000 7`: one Lean job per G9 group, `-j1 -M7000
-DElab.async=false`, MemoryHigh=5 GiB, MemoryMax=7 GiB, MemorySwapMax=0,
TasksMax=128, timeout=900 seconds. Each admission reported 24+7 GiB against
the 55 GiB reservation ceiling. No local/dependency/package build or cap
change occurred. All attempted source hashes are distinct; no unchanged
successful or failing source was rerun.

| Attempt | Source SHA-256 | Lean/scope exit | Wall s | Peak RSS KiB | Swaps | Status |
|---:|---|---:|---:|---:|---:|---|
| 1500 | `eb80665e213b96b5b320190ed0721e9260d072047bd65cc5b0d2a6cd03502d15` | 1 | 1.66 | 3323440 | 0 | Independent layer: conditional and Fin-cast elaboration errors; one unused simp warning |
| 1501 | `b4bf0982e088c42335913c3b6af0caee640130e1d4ceda0413f550e5216cfc50` | 1 | 1.67 | 3323116 | 0 | Two remaining explicit Fin/cell conversion goals |
| 1502 | `01f4517d1a10119cf48b5db6192e220445d7efa155c66105e38bf94a6e0f5184` | 0 | 1.65 | 3332864 | 0 | Independent layer green; 11 theorem and 5 abbreviation audits; no warnings |
| 1503 | `7ebb799fe838a9e50459d9e3b2c99b69b3a77c5849a01047a62c2952e8226370` | 1 | 1.81 | 3329044 | 0 | Added fixed-link chain; nullifier salt-tail Fin conversion remained |
| 1504 | `5ade1ed6f87ee3f2140ecdf80e04e0d50d64d8b25452808c5afd36713ac7815c` | 0 | 1.91 | 3340988 | 0 | Owner/commitment/nullifier and generic node-input layer green; one unused simp argument |
| 1505 | `43cc90483c01df3911bd7c5dbcfe8333b85d209388f552193d66e7940b4f08fd` | 1 | 2.14 | 3334164 | 0 | Complete theorem added; two node row-zero Fin projections and one induction-bound projection remained |
| 1506 | `a6ebcab070726508d50eb24837ae74633f00de18841d8614d5cf8b1625138e0e` | 0 | 2.17 | 3351676 | 0 | Complete frozen development pass against final G8 object; 24 permitted audits, no warnings |
| 1598 | `1b0f05c9252142fb659e2eaad2d528c42c9dbc405668e1e982d891ba424ca019` | 0 | 2.18 | 3351276 | 0 | Coordinator final pass after adding provenance and explicit interface audit; 24 permitted audits, no warnings |

The coordinator authorized an early independent-helper check while G8 was
being built. Accordingly, attempts 1500–1502 omit the still-unused
`CopyInputLinks` import and its two dependent hash-chain helpers; the full
draft was saved before that focused stage. Attempts 1503 onward restore the
dependency and helpers. Green 1502 and 1504 are intermediate evidence only;
1506 checks the complete final theorem against G8's finalized 1498 object.
G9 paused new builds during the G8 finalization hold.

All 19 theorems, including every private helper, have explicit axiom audits,
as do all five new abbreviation helpers. At 1506 every theorem uses exactly
`[propext, Classical.choice, Quot.sound]`; `extractionChunk`,
`extractionOutput`, and `extractionCurrent` use `[propext, Quot.sound]`, and
the remaining two abbreviations use the three permitted axioms. There are
24 named declarations and 24 distinct audit commands, with no missing or
extra entries. No prohibited proof construct or trailing whitespace was
found. Compiler error terms from failed attempts are rejected as evidence.

Each run retained exact `evidence/source-N.lean`, `evidence/sha-N.txt`,
`evidence/out-N.log`, and `evidence/time-N.log` records on the build host,
plus `/tmp/r0-extraction-20261008/Extraction-N.lean` locally. The actual
scope status and `/usr/bin/time` status agree for every run; classification
does not use the outer runner's shell success. Final local and remote
source hashes match. After independent full source review, the coordinator
added only precise provenance/model-hash/method comments and
`#check @input_note_extracted`, producing the distinct 1598 source snapshot;
no theorem statement or proof changed. Final check 1598 admitted 24+7 GiB,
passed with matching scope/time exits zero, and confirmed exactly the six
requested hypotheses and `InputNoteExtracted pub A` conclusion without
extra premises. Its `source-1598.lean`, `sha-1598.txt`, `out-1598.log` and
`time-1598.log` are retained in the same evidence directory. The final frozen
source SHA is `1b0f05c9252142fb659e2eaad2d528c42c9dbc405668e1e982d891ba424ca019`;
no further G9 build is needed.

## G10: Generic SEM bad-set lemmas

`SemBadSets.lean` is a Mathlib-only proof file for the four requested finite-field cardinality obligations. It proves: (1) the univariate nonzero-root bound; (2) a general coordinate-cylinder union bound for arbitrary `bad : Fin n → Finset K` and its nonzero-polynomial sumcheck specialization; (3) the arbitrary-`n` individual-degree-one zero bound by the cached Mathlib Schwartz–Zippel theorem, including the `n = 0` case; and (4) distinct literal multisets of degree-at-most-16 polynomials have distinct outer products, with a nonzero coefficient whose inner degree is bounded by `16 * max S.card T.card`. No probability claim or source-semantic correspondence is made.

The cached named theorem used in (3) is `MvPolynomial.schwartz_zippel_sum_degreeOf` in `Mathlib/Algebra/MvPolynomial/SchwartzZippel.lean` (pinned mathlib source in `ZK-v7-one-tx-formal-consolidation-20260828/AspisFormal/.lake/packages/mathlib`). Its hypotheses are `[CommRing R] [IsDomain R] [DecidableEq R]`, `hp : p ≠ 0`, and `S : Fin n → Finset R`; it bounds the rationalized zero count divided by the product of set cardinalities by the sum of individual degree/cardinality ratios. With `S i = univ`, the proof specializes this symbolically and handles `n=0` separately. Other support for (4) is `Polynomial.roots_multiset_prod_X_sub_C` (`Mathlib/Algebra/Polynomial/Roots.lean:307`) and `Polynomial.coeff_X_sub_C_mul` (`Mathlib/Algebra/Polynomial/Degree/Operations.lean:126`).

The coordinator independently reviewed the complete final source, the public statements, and the cited Mathlib lemmas. Cached Mathlib revision: `81a5d257c8e410db227a6665ed08f64fea08e997`; SchwartzZippel.lean SHA-256: `c8430c74c8f84ea5c97d8171bec22c5424ddba5d2bf2b7b16752e414db2a4993`. The exact cited Schwartz–Zippel declaration is at lines 179–185. The nonzero-round premise in the polynomial specialization matches SemLedger's nonzero round-difference branch; `round_bad_union_card` separately states the requested union bound from the per-round cardinality hypothesis alone. Neither result assumes `0 < n`.

Host: `dombarker@100.108.41.90`, workspace `/home/dombarker/project-offloads/aspis-fs-generic-20261006`; Lean `leanprover/lean4:v4.32.0` (`LEAN_GITHASH 8c9756b28d64dab099da31a4c09229a9e6a2ef35`), cached pinned mathlib library path as above. Development attempts 1600–1602 used the Mathlib-only `run.sh N R0P/SemBadSets` (`evidence/run.py`, `objects`); attempts 1603–1605 used `run2.sh N R0P/SemBadSets 4500 7` (`evidence/run2.py`, `objects2`, explicit `M-limit=4500`). Both runners used `MemoryHigh=5G`, `MemoryMax=7G`, `MemorySwapMax=0`. For attempts 1603–1605, manual reservation inspection showed 24 GiB populated + 7 GiB new cap = 31 GiB, below 55 GiB. The runner itself printed the same check. No cap change occurred. Current repo HEAD at first successful source was `a22519dc846c64f3fb84906b367032b5d47c51a9`.

| Attempt | Source SHA-256 | scope exit | inner/time exit | wall | peak RSS | swap | audits / notes |
|---|---|---:|---:|---:|---:|---:|---|
| 1600 | `7bdb9f1f935fc87957b4c47a1db93088213a2297fe9e4501a3fa910fba220247` | 1 | 1 | 2.45s | 3,319,052 KiB | 0 | Elaboration/proof errors; compiler error-term audits rejected. Exact draft source was not archived. |
| 1601 | `14cb14195518ea64605bb195638ac6396b8e333b0e37999568592b242fa5266d` | 1 | 1 | 2.91s | 3,318,068 KiB | 0 | Elaboration/proof errors; compiler error-term audits rejected. Exact draft source was not archived. |
| 1602 | `9c5b058ad0145925f2cc03ea9018caa57ddac0013abc829e8a94c671b7cd83d1` | 1 | 1 | 3.35s | 3,319,472 KiB | 0 | Elaboration/proof errors; compiler error-term audits rejected. Exact draft source was not archived. |
| 1603 | `4c8d4aa12fe438a7681b15dfeecd048e9838eab50d62d58ab1547f8e4c8b6a3a` | 0 | 0 | 2.22s | 2,111,788 KiB | 0 | Passed; one unused `[Field K]` linter warning; 8 `#print axioms`, all allowed. |
| 1604 | `8cea7af99ed488febd7bcd2181ce5db956714e3eafef115d4ffe088c792bf800` | 1 | 1 | 2.32s | 2,100,656 KiB | 0 | Changed source to remove warning but placed `omit` after a doc comment; syntax error. Rejected despite 8 permitted audits. |
| 1605 | `f45db9d42d6e396e43c99b1d8b6a0357223a2e248b463baf0ce1b665bd681dc8` | 0 | 0 | 2.36s | 2,109,504 KiB | 0 | Passed without warnings; 8 `#print axioms`, all exactly `[propext, Classical.choice, Quot.sound]`. |
| 1698 | `aede759383ff9791301e45fc63acf21e6c7bb1a2f56f7eb37a113de2d2a8f15c` | 0 | 0 | 2.34s | 2,110,400 KiB | 0 | Coordinator final pass with 8 permitted audits, no warnings, and all five public signatures printed. |

The coordinator added precise model/Mathlib provenance and five public `#check` commands to the passing 1605 source, without changing statements or proofs. Final check 1698 used the Mathlib-only `run.sh 1698 R0P/SemBadSets`: `-j1 -M4500 -DElab.async=false`, the same 5G/7G/0 scope, TasksMax=128 and 900-second timeout. Its manual reservation check recorded 24+7 GiB against the 55 GiB ceiling in `evidence/reservation-1698.txt`. All seven attempt hashes are distinct. No cap change, unchanged rerun, local compilation, or dependency rebuild occurred.

Evidence limitation: exact source snapshots for attempts 1600–1604 were not archived. Their SHA, stdout, and timing records remain available. The failed 1600–1602 outputs contain elaboration errors and `sorryAx` audit entries; they are rejected as proof evidence. An interim report inferred authored `sorry` placeholders from those entries. That inference was unsupported and is withdrawn: the logs contain no “declaration uses sorry” warning, and unavailable source snapshots cannot be scanned retrospectively. No authored placeholder is established by those diagnostics.

The exact successful 1605 source is retained at `/tmp/r0-extraction-20261008/g10-evidence/SemBadSets-1605.lean`, SHA `f45db9d42d6e396e43c99b1d8b6a0357223a2e248b463baf0ce1b665bd681dc8`. Final 1698 is retained as host `evidence/source-1698.lean` and local `/tmp/r0-extraction-20261008/SemBadSets-1698.lean`; its `sha-1698.txt`, `out-1698.log`, and `time-1698.log` records are retained in the host evidence directory; final local/host SHA is `aede759383ff9791301e45fc63acf21e6c7bb1a2f56f7eb37a113de2d2a8f15c`. Scope/time exits agree for every recorded attempt. Raw development records are `evidence/sha-N.txt`, `evidence/out-N.log`, and `evidence/time-N.log` in the build workspace and copied under `/tmp/r0-extraction-20261008/g10-evidence/`.

The final source has seven theorems and one named helper definition, all eight explicitly audited with only `propext`, `Classical.choice`, and `Quot.sound`. It contains no prohibited proof term. All finite-set and multiset arguments are symbolic; no concrete universe is enumerated. No statement gap or mathematical stop remains.

### Continuation G10: function-level SEM composition obligations

The continuation extends the explicitly requested `SemBadSets.lean` and imports the fixed `R0P.Zerocheck` interface. All eight prior generic declarations and their proofs remain unchanged. No other existing Lean file was edited. Starting and review revision: `573bde72536f96ea6645ddd1fae7ad838932ade8`; the fixed lead interfaces are from `a22519dc8`. `Sumcheck.lean` SHA-256 is `4d14c4f8e6488e39e0a8c50ada54f6116c489214bc0e0e7c827b4aedab2a599a`; `Zerocheck.lean` SHA-256 is `6e6b88599348de3f314a074e1396f5034d019ef4210d06a3ecce65a6ff53d14f`. Local and cached host sources match these hashes.

All five requested obligations are proved:

- `badMu_card` and `badTheta_card` state the unconditional bounds 2 and 28 on `Finset.univ.filter`. The definitions' nonzero-support conjuncts are handled internally; the zero-support branch is empty. The nonzero branches use the retained `univariate_bad_card`, whose proof uses `Polynomial.card_roots'`. Theta coefficients are isolated symbolically at a witnessing row and lane.
- `mle_bad_card n f (hf : f ≠ 0)` proves the general `n * |K|^(n-1)` bound by recursion on `n`. Writing the leading-coordinate polynomial as `A(v) + x * (B(v)-A(v))`, the proof partitions zeros into both-endpoint-zero fibers and the remainder. The former are bounded using a nonzero Boolean branch and the induction hypothesis; the latter inject into their tails by uniqueness of an affine root. `badZc_card` gives the unconditional `10 * |K|^9` specialization. Neither new proof uses `MvPolynomial`; the earlier, separate generic Schwartz–Zippel theorem is retained without being used by this induction.
- `badAlpha_strategy` states the exact ten-round accepted-false filter event and bound `10 * 27 * |K|^9`. The only semantic premise is `IndDeg 27 10 G`; acceptance supplies the observed round-degree checks. A generic arbitrary-round/degree/claim theorem fixes the earlier challenges before bounding each next-coordinate root set, counts fibers, and recursively restricts the strategy. The proof strengthens the recursive argument of `Sumcheck.sound` locally because that theorem's existential conclusion alone does not retain the prefix dependency. It adds no global degree assumption on the strategy and makes no probability claim.
- `MLDeg` recursively gives degree-bounded polynomial dependence on the leading variable for every tail and preserves the bound under all leading restrictions. `mlDeg_indDeg` proves the implication to the fixed `IndDeg`. The closures cover `eqwB` with a fixed Boolean argument, recursive MLE evaluation, products with added degree bounds, sums with their maximum, scalar multiples, and symbolic finite sums. `indDeg_of_multilinear_product` is the named product-to-`IndDeg` bridge.

The brief's prefix expression `Fin.castLE j.isLt.le j` was ill-typed for `j : Fin i`: the required embedding bound is `i ≤ 10`, not `j.val ≤ i`. The user explicitly approved correcting only this expression to `Fin.castLE i.isLt.le j`. The final public theorem prints that corrected prefix, with the original event and numerical bound unchanged.

No new theorem evaluates a trace, a row range, a constant table, a permutation, or a concrete field/row universe. Counts use symbolic root bounds, finite-set identities, and dimension induction. The zero-dimensional cases prove the bad predicate empty. The coordinator reviewed all source/proof changes and the printed final public signatures; independent read-only reviews confirmed the fixed premises and both counting arguments.

#### Focused build evidence

Only the cached host `dombarker@100.108.41.90`, workspace `/home/dombarker/project-offloads/aspis-fs-generic-20261006/`, was used, with pinned Lean 4.32.0. Every target was `R0P/SemBadSets`, through `run2.sh`; one G10 job ran at a time. Cgroup limits stayed `MemoryHigh=5G`, `MemoryMax=7G`, `MemorySwapMax=0`, with TasksMax=128 and a 900-second timeout. Runner reservation admissions were 24+7 GiB except 1613 at 26+7 GiB, all below the 55 GiB ceiling. No local compilation, package/dependency rebuild, or unchanged-source rerun occurred.

Resource-argument deviation: attempt 1606 mistakenly passed Lean `-M7000` instead of this group's prior `-M4500`, while retaining the same 5G/7G/0 cgroup. This was disclosed when noticed. Attempts 1607 onward restored `-M4500`; no failure was rerun with a larger cap. The exact timed runner commands are retained.

| Attempt | Source SHA-256 | Scope/time exit | Wall | Peak RSS KiB | Swap | Permitted audits/total | Result |
| --- | --- | --- | --- | ---: | ---: | ---: | --- |
| 1606 | `fd72de150ff9a891ba5d00f553f11cfcccc099cef20e02ecfaf13fcfd1c2aad9` | 0/0 | 0:02.67 | 2,117,304 | 0 | 21/21 | MLDeg layer passed; partial source only. |
| 1607 | `b3b5176d666752797c16a40cf1ddaeb484ee1da0057a3a3117d829267061ef9e` | 1/1 | 0:03.69 | 2,119,832 | 0 | 24/30 | Bad-set draft failed: declaration context, polynomial APIs, MLE and finite-set elaboration. |
| 1608 | `0ed84ae845b6b9ae0ce439fe18d761119a89c80fa36a4e9293112459d926ddd9` | 1/1 | 0:03.22 | 2,125,836 | 0 | 26/31 | Fiber-count helper passed; strategy layer failed on prefix/accept/count/filter elaboration. |
| 1609 | `044c75410afa91a266a3aafd04c84babd84502d132a02903a84b7af5891611bb` | 1/1 | 0:04.27 | 2,130,668 | 0 | 25/31 | Bad-set draft failed: hidden filter decisions, coefficient API, polynomial simp loop, MLE rewrites. |
| 1610 | `66d01efb748065c494202e1e9766821e7a40c39f66eb3ccc526eccc52fb45847` | 1/1 | 0:03.19 | 2,127,608 | 0 | 26/31 | Strategy layer failed on dependent Fin.cons typing and specialized filter transport. |
| 1611 | `1bc8738088071cd4d2ed612698ad6eb8969445fb449208b7aa70f589a21a7382` | 1/1 | 0:03.96 | 2,134,296 | 0 | 27/31 | Bad-set layer failed on coefficient equality orientation and R0 filter transport. |
| 1612 | `ad9abba0e9d58179c9ce5b8584f397f817ab6c5cd5352386945149a716e5baa3` | 1/1 | 0:03.17 | 2,127,564 | 0 | 30/31 | Generic adaptive theorem passed; specialized filter still needed whole-function unfolding. |
| 1613 | `86b3b65e33c73d9c9b61faa205f29a70a6a03983dea134f937c9e58a91961639` | 0/0 | 0:04.56 | 2,159,560 | 0 | 41/41 | Complete file passed; one unused simp-argument warning. |
| 1699 | `b74e1d7adfaaf6ad0c4973b96461b6359d23b62d6cadb6e2983646d3e5b40b5d` | 0/0 | 0:04.64 | 2,162,908 | 0 | 41/41 | Final complete pass; no warnings; public signatures printed and reviewed. |

1606 contained the original file plus MLDeg; 1607/1609/1611 checked the bad-set layer, while 1608/1610/1612 checked the independent adaptive layer. Intermediate passing declarations were not accepted as a full-file result. Attempts 1613 and 1699 contain all requested declarations. Failed elaborations emitted `sorryAx` error-term audits; those attempts are rejected. Every exact source snapshot in this continuation was retained and scanned; there are no authored placeholders or prohibited options.

Before final coordinator check 1699, the sole unused simplifier argument was removed and provenance/method comments plus 13 public `#check` commands were added. This produced a distinct source hash. Final 1699 passed with matching scope/time exits zero, 4.64 seconds wall time, 2,162,908 KiB peak RSS, zero swap, no warnings, and 41 matching permitted axiom audits. The 33 new named declarations and all eight retained declarations are audited, including private helpers. Only `propext`, `Classical.choice`, and `Quot.sound` occur; some declarations need fewer or no axioms.

Final frozen source SHA-256: `b74e1d7adfaaf6ad0c4973b96461b6359d23b62d6cadb6e2983646d3e5b40b5d`. Each host `evidence/source-N.lean` matches `evidence/sha-N.txt`; raw `evidence/out-N.log` and `evidence/time-N.log` retain actual scope/Lean status, independent of the outer runner's return code. Local mirrors are `/tmp/r0-composition-20261008/SemBadSets-N.lean` and `/tmp/r0-composition-20261008/evidence/`. Coordinator and independent attempt inventories are retained there. All nine attempt hashes are distinct. G10 has no remaining mathematical stop; no production lane equivalence or probability claim follows from these lemmas alone.

## G11 source audit: semantic scalar and packed theta lanes

Read-only source audit at worktree HEAD `573bde72536f96ea6645ddd1fae7ad838932ade8`; Rust inspection pin `e4d68a70d3f6beb215c9f6dd418f4a2a3740c809`. Pinned source SHA-256 values:

- `pair_forest_semantic_terminal.rs`: `efbc5be87e271419d7b09e1bb6e3a83984d42795bc20067ea039814fb89ffa58`
- `pair_forest_copy_terminal.rs`: `50062fff8b6afbffad3ddbb8eda09992353a9171c4955151cece26a654c6a6d5`
- `pair_forest_hiding.rs`: `61bcd59a22c9c02fe3f9ba69cda43bfa8fe02ea14f15da9b761e976fe48798bf`

### Scalar slots and packed groups

The terminal declares 94 indexed semantic source lanes (pair-forest terminal line 35) and 24 packed semantic groups (line 36). The ordered scalar contributions are:

| Scalar slots | Count | Family/source construction | Destination packed groups |
| --- | ---: | --- | --- |
| 0–15 | 16 | Initial schedule residuals | 0–3 |
| 16–31 | 16 | Schedule absorption residuals | 4–7 |
| 32–48 | 17 | Path residuals | 8–12 |
| 49–83 | 35 | Value residuals: 33 range plus 2 conservation | 12–20 |
| 84–91 | 8 | Public digest binding residuals | 21–22 |
| 92–93 | 2 | Scalar/asset residuals returned by `scalar_lanes` | 23 |

Thus the broad family intervals are contiguous: schedule 0–31, path 32–48, value 49–83, digest 84–91, scalar/asset 92–93. The source calls show these starts and lengths: schedule initial at offset 0 and absorption at 16 (`:381–391`); path array length 17 at offset 32 (`:394–427`); value range length 33 at offset 49 and conservation length 2 at offset 82 (`:466–519`); digest length 8 at offset 84 and scalar length 2 at offset 92 (`:1143–1182`). Range and conservation are one broad value family here.

The final scalar contributions at offsets 0–11 also receive occupancy residuals. `add_schedule_lanes` accumulates `initial[0..15]` at offset 0, and `add_occupancy_lanes` separately accumulates `occupancy[0..11]` at that same offset (`:381–391`, `:529–554`). Therefore for each scalar position `j ∈ 0..11`, the contributions are `initial[j] + occupancy[j]`; their four-lane packed group receives both `qm31_pack_base4(initial[4g..4g+4])` and `qm31_pack_base4(occupancy[4g..4g+4])`, where `g = j / 4`. Occupancy does not extend the indexed 94-slot source interval; it is an additional summand on final slots 0–11.

The packed group map is:

| Packed group | Scalar contributions |
| ---: | --- |
| 0 | initial 0–3 plus occupancy 0–3 |
| 1 | initial 4–7 plus occupancy 4–7 |
| 2 | initial 8–11 plus occupancy 8–11 |
| 3 | initial 12–15 |
| 4–7 | absorption 16–31 |
| 8–11 | path 32–47 |
| 12 | path 48 plus value 49–51 |
| 13–19 | value 52–79 |
| 20 | value 80–83 |
| 21–22 | digest 84–91 |
| 23 | scalar 92–93 plus zero padding in component positions 2–3 |

`add_preweighted` maps scalar source `4 * group + slot` to component `slot` of `qm31_pack_base4`, zero-padding positions outside each interval (pair-forest terminal `:106–124`). `semantic_packed` accumulates schedule, path, value, occupancy, digest, then scalar contributions (`:1143–1182`). Its path call covers scalar 32–48 (`:394–427`); the value calls cover 49–83 (`:466–519`). The concrete cross-family group is group 12: it contains path slot 48 and value slots 49–51. Groups 0–2 also combine occupancy and schedule. This is the requested mixed-family stop condition; no `LaneMap.lean` definition or proof was written.

### Selector bit order

At the pinned `pair_forest_copy_terminal.rs:143–177`, `Selectors::expand` processes coordinates in order and splits each parent weight into `(1-coordinate)` at `2*index` and `coordinate` at `2*index+1` (`:144–158`). The first coordinate therefore becomes the most significant bit of the resulting array index; later coordinates append lower-order bits. `at_point` passes `point[0..6]` to the 64-entry high selector and `point[6..10]` to the 16-entry low selector (`:161–166`); `boxed_at_point` is exactly `Box::new(Self::at_point(point))` (`:168–171`). Row lookup is `high[row >> 4] * low[row & 15]` (`:173–177`). Thus Boolean coordinates `point[0]..point[5]` are block bits 5 down to 0, and `point[6]..point[9]` are local-row bits 3 down to 0: the 10-bit row index is big-endian in coordinate order.

The pinned `pair_forest_hiding.rs` uses rows as `block * 16 + local` for path/value bounds (`:41–46`); active-row masks select block by `row >> 4` and local bit by `1 << (row & 15)` (`:190–196`). This agrees with the selector's high/low split and confirms the row/column layout relevant to G11.

### Theta coefficient powers

`composition_parts` initializes the accumulator to `copy.residual`, then traverses semantic lanes in reverse and Poseidon lanes in reverse with `composition := theta * composition + lane` (pair-forest terminal `:1267–1274`). Expanding the Horner fold gives Poseidon lanes 0–3 powers θ⁰–θ³, semantic packed groups 0–23 powers θ⁴–θ²⁷, and copy residual power θ²⁸. This matches `lanesComp`'s increasing-power definition (`Zerocheck.lean:84–85`). A proposed `lane0copy` assignment conflicts with both the Rust fold and Lean definition.

### Separate proposal-only Positive adapter

`Positive.lean:3–7` labels `Positive.lean` as a research-only G1 adapter, not asserted to be enabled by a production feature, with no packing or extraction claim. Its comment cites proposal witness `ROW=1014, COL=3, LANE=94` (`:11–12`). The `positiveResidual`/`positiveRowClaims` adapter is at `:14–25`; the standalone `positiveFamily` is at `:27–30`. Production instead declares 94 source semantic positions 0–93 and `semantic_packed` constructs only its 24 packed outputs (`pair_forest_semantic_terminal.rs:35–36,1143–1182`). Proposal lane 94 is not a 95th production scalar input and does not establish a production `positiveFamily` lane.

### Smallest proposed interface corrections (not enacted)

- Define the production theta-lane interface in source order: Poseidon indices 0–3, semantic packed indices 4–27, and copy index 28. Do not call copy `lane0`.
- State the scalar-to-packed interface at the 24-group level, including the additive occupancy contribution to groups 0–2 and the mixed path/value contribution to group 12. With base-typed components, packing injectivity could separate the distinct Path and Value component positions in group 12, but the explicit mixed-family stop instruction applies. At scalar slots 0–11, packing injectivity gives zeros of the schedule-plus-occupancy sums; separating those summands additionally needs the source selector facts. The lead must authorize a mixed-group interface before this proof continues.
- Keep proposal `positiveFamily`/lane 94 separate from the production lane map; do not extend the production scalar catalogue to 95 based on that proposal citation.

No build was run. The coordinator reviewed the source ranges independently; all three files match the inspection pin. No existing Lean source was edited. This is a source mapping, not a lane-map theorem or a proof that packed lane zero implies each source-family residual vanishes.

The coordinator source review, including hashes of each cited range, is retained at `/tmp/r0-composition-20261008/G11-source-review.json`. No Lean target was needed for this source-stop finding; attempts 17xx remain unused.

### Continuation G11′: public-input base-typing stop

Resumed after the accepted lead decisions at `d43cf35be120f0fce7be494b5b86e3a17de712d6`. Fetch/fast-forward found the branch current; subsequent lead commits through `e1b73deae8e8f00a153d04ca8ed8f44478da77c0` were present at the final source review. The approved theta order, mixed groups, and production-family list above are retained. A further interface mismatch prevents the requested proof that every packed scalar residual belongs to the base subfield.

`BaseTyped F t` quantifies only over trace cells in columns below 26 (`CoreExt.lean:26–28`). `Public K` instead stores `assetId`, optional withdrawal amount, and all digest coordinates as arbitrary elements of `K` (`Core.lean:47–67`); its comment about embedded base-field digests is not a membership hypothesis. `pack4_eq_zero_iff` requires each of its four components to belong to `F` (`CoreExt.lean:41–42`). No public-input base-typing predicate or corresponding premise is supplied by the fixed interface.

A single failing component is scalar source slot 92, semantic packed group 23, component 0, hence theta lane 27. At row 44 its value is exactly `t 1 44 - pub.assetId`: `assetFamily` selects row `2*16+12` in its first residual (`Asset.lean:21–30`). Base typing supplies `t 1 44 ∈ F`; it cannot supply `pub.assetId ∈ F`. In fact, for any `B : PackBasis F`, `B.i ∉ F`: otherwise its `indep` property applied to `(-B.i, 1, 0, 0)` would force `1 = 0`. Taking the zero trace and `pub.assetId = B.i` therefore gives a base-typed trace whose slot-92 residual at row 44 is `-B.i ∉ F`. This is a mathematical counterexample to the requested unconditional scalar-membership obligation, independently reviewed against the definitions; it is not a newly kernel-checked theorem or a counterexample to the entire global vanishing equivalence.

The source does supply the missing property before abstraction. At the pinned terminal, `SemanticPublic.asset_id` has type `M31` and the amount has type `Option<u32>` (`T:87–98`); `lift_m31` embeds into QM31 (`T:100–103`). The asset and withdrawal residuals explicitly subtract these lifted base values (`T:1165–1181`), with amount validation at `T:1234–1239`. Rust `Digest` is `[M31; DIGEST_ELEMS]`, with eight elements (`poseidon2.rs:58–60`); digest binding subtracts `lift_m31(target)` after any M31 right-tweak addition (`T:364–377`). The Lean public record retains the lifted values but no proof of their membership in the chosen subfield `F`.

The missing public-field coverage also includes the enabled targets in packed slots 84–91 (`Digest.lean:65–88`): anchor, nullifier, change and next root; recipient whenever its Option is present, independently of variant; snapshot-frontier coordinates on the nonzero append-bit branch; and next-frontier coordinates at the carry entry when carry is below 20. The withdrawal amount is needed when the variant is withdrawal and the Option is present. The empty-root branch remains the frozen integer-constant target and needs no new public premise.

Smallest proposed interface change, not enacted: supply public base membership for `assetId`, the enabled withdrawal amount, and each enabled digest target coordinate, or supply a base-typed public representation with a proved conversion to the existing `Public K`. For the displayed counterexample alone, `pub.assetId ∈ F` is necessary and sufficient to repair the missing component membership. Choosing the complete public-typing contract and adding it to the lane-map theorem remains a lead interface decision; no premise was added or weakened here.

No packed semantic input reads a trace column at or above 26. `rowOpenings` has `Fin 16` input columns (`Core.lean:30–43`), and the Poseidon state columns are likewise 0–15 (`Poseidon.lean:754–757`). H1 at column 26 belongs only to the separate, unpacked Copy lane 28. The new stop is public-input typing, not a trace-column, mixed-family, selector-order, or Positive-lane issue.

Source review uses Rust inspection pin `e4d68a70d3f6beb215c9f6dd418f4a2a3740c809`; all inspected Rust files match that pin. Relevant unchanged SHA-256 values:

- `Core.lean`: `eba6bb784803b5f00922724efc9997a8d5ab6bc55cd8c100bffd8a397dabe1f9`.
- `CoreExt.lean`: `de191f5bf4ca0389c7b9e0ee613982888a97ec9810072913c19054882364e56b`.
- `Asset.lean`: `2c36ba0a589d2e982ca55716f5093e6c5da4152454f24de26c71f9ad9d9ef424`.
- `Digest.lean`: `928d531c7ae80fdb2a3865bf3b2eac2d1dea84c2892c413f5c4a63709947d26b`.
- `pair_forest_semantic_terminal.rs`: `efbc5be87e271419d7b09e1bb6e3a83984d42795bc20067ea039814fb89ffa58`.

Stopped as instructed on this further source/interface mismatch. No `LaneMap.lean` file, new theorem, Lean build, or local substitute build was created; no 17xx attempt was consumed. Build exit, wall time, RSS, swap and new axiom audits are therefore not applicable. No existing Lean source was edited. Coordinator range hashes and the independent public-input inventory are retained at `/tmp/r0-lanemap-20261008/source-review.json` and `/tmp/r0-lanemap-20261008/public-typing-audit.md`.

### Continuation G11′: completed lane map with PublicBase

Resumed after lead commit `0d8ed6e63`, with the authorized `hpub : PublicBase F pub`; source base through `e91642e9c`. The earlier public-input typing stop is resolved by that lead definition. No existing Lean source was edited. The new `LaneMap.lean` imports the production families, CoreExt and Zerocheck, and implements the exact agreed lane catalogue.

- `rowOf` encodes coordinates most-significant first. `rowCode_testBit`, the explicit `rowBits` inverse, and `rowOf_bijective` establish the address convention without enumerating rows. Coordinates 0–5 give block bits 5..0 and 6–9 give local bits 3..0 (`pair_forest_copy_terminal.rs:143–177`; `pair_forest_hiding.rs:41–46,190–196`).
- `scalarLane t pub : Fin 94 → (Fin 10 → Bool) → K` reads the ported residual lists in source order: Schedule 0–31, Path 32–48, Value 49–83, Digest 84–91, Asset 92–93; Occupancy is added at 0–11. The private proof bridges retain all entries, including prescribed zero cells. `scalarLaneRow` supplies the explicit zero padding at 94–95.
- `laneOf t pub lam chi B` has Poseidon packed indices 0–3, semantic packed indices 4–27, and Copy at 28 with H1 = trace column 26. This is the exact power order of the source's reversed Horner folds (`T:1267–1274`); packing uses consecutive source slots (`T:106–124,1143–1182`).
- `schedule_occupancy_separate` proves both directions of separation over every row and each of the first twelve scalar positions, using local-row-zero schedule support and occupancy rows 1017/1018. The other mixed group (Path 48, Value 49–51) is separated by distinct pack4 components.
- `lanes_zero_iff_holds` proves exactly the eight production-family conjunction under `BaseTyped F t`, `B : PackBasis F`, and `PublicBase F pub`: Value, Occupancy, Asset, Schedule, Path, Digest, Poseidon scalar, and Copy via CHolds. Each semantic residual is shown to belong to F using the trace and public typing contracts, before applying `pack4_eq_zero_iff`. The existing Poseidon packed/scalar equivalence handles its four groups. No Positive hypothesis or conclusion is added.
- `bsumB_rowOf`, `lane_h1_sum`, and `lane_inactive_sum` provide the Boolean-coordinate/Fin-1024 correspondences requested by the LogUp glue. The inactive helper retains the literal `(1 - active) * H1` form (`T:1307–1308`). These identify sums; they do not assert vanishing.

All packed trace inputs are columns 0–15. Column 26 is used only by the unpacked Copy lane and helper sums. The Poseidon raw-limb-to-canonical-field refinement obligation remains as recorded; this lane theorem uses the already-proved field-level packed family. No probability claim, tuple-extraction premise, or reinterpretation of source lanes was introduced. Coordinator and independent reviews checked the final statement, offsets, selector bit order, padding, source operations and public typing.

#### Focused builds and audits

All jobs used the pinned Lean 4.32.0 build host/cache and `run2.sh N R0P/<target> 7000 7`, MemoryHigh 5 GiB, MemoryMax 7 GiB, MemorySwapMax 0. Each reservation was 24 + 7 GiB. Attempt 1700 was the explicitly requested CoreExt rebuild into the shared R0P objects directory; subsequent targets were R0P/LaneMap. No local build, dependency rebuild, cap increase, unchanged failing rerun, or simultaneous G11 job occurred.

| Attempt | Scope/Lean exit | Time exit | Wall | Peak RSS KiB | Swaps | Source SHA-256 |
| --- | ---: | ---: | ---: | ---: | ---: | --- |
| 1700 | 0 | 0 | 0:01.43 | 3327464 | 0 | `7b0a6820f1f6d446943447509edd40babf84801eb1f06aeabd868ff033d41188` |
| 1701 | 1 | 1 | 0:03.58 | 3332340 | 0 | `f3b7afdbf1942083b1fc9331e7b8e567e0eafad6d4f31a76ece7a20fb8c75798` |
| 1702 | 1 | 1 | 0:04.90 | 3327048 | 0 | `ac0c6e80db0d9e3b09f39b9cd8ac455db06c9f03b268cdbbfb041bb9d1fc3dc7` |
| 1703 | 1 | 1 | 0:03.26 | 3332972 | 0 | `7725ed7acd8a70dd75c57133f78de8e0770d26cec5f9f9a5c3cacea69f83271e` |
| 1704 | 1 | 1 | 0:09.19 | 3374052 | 0 | `d1f0c507624b2e39c62b9e7fd85b0b165aae0c9c18e68dc903e8aba5d0911160` |
| 1705 | 1 | 1 | 0:09.77 | 3380940 | 0 | `d2354154191eeb0bd9031c868f5621360f77f0b2fe8ef20624a731b9c1b07cec` |
| 1706 | 1 | 1 | 0:03.37 | 3334464 | 0 | `6bfb10a9d651f8404366e97049f59764fb84fce9d6050003390e4f5d2e50d17b` |
| 1707 | 1 | 1 | 0:09.20 | 3383004 | 0 | `f346d646d1f2cfd378cfabe9c4182420ed71aab2382de6cfe800b7d3136ae5f5` |
| 1708 | 0 | 0 | 0:09.27 | 3411784 | 0 | `7f27bb9e3ece27b76316bb61a9219ebf10452d5365d7f5f44e08a1387f67d95e` |
| 1799 | 0 | 0 | 0:09.38 | 3412060 | 0 | `122aa0b15111da62ae6672051c43a1cfe792e6cd240974669af87732539f6e17` |

Attempts 1701/1703 checked the row/support layer: the rejected errors were Fin case/bit APIs, selector numeral projections, and a missing rowOf unfolding. Attempt 1702 checked family membership: zero-target membership and using a known selector fact before decomposing its product required corrections. Attempts 1704/1705/1707 checked the combined file and were rejected for list-index transport, explicit finite-index bounds, zero padding, and tactic indentation. Attempt 1706 separately checked the symbolic helper-sum bridge and was rejected for an already-closed goal and an implicit reindexing function. Failed elaborations emitted `sorryAx` through error terms; none was accepted and no placeholder was authored. All source hashes are distinct.

Attempt 1708 passed the complete combined implementation. The coordinator then froze the repository source with provenance comments and one namespace, and ran final focused check 1799. Final scope/Lean and time exits are zero, wall 9.38 seconds, peak RSS 3,412,060 KiB, swaps zero, no warnings. All 44 named declarations have matching `#print axioms` commands; every theorem, including private helpers, is covered. The final audits contain only `propext`, `Classical.choice`, and `Quot.sound` (some declarations need fewer or none). The source scan found no prohibited proof terms/options, and no normalization of a trace, row universe, constant table, or permutation.

Final frozen `LaneMap.lean` SHA-256: `122aa0b15111da62ae6672051c43a1cfe792e6cd240974669af87732539f6e17`. Raw host evidence is `evidence/out-N.log`, `time-N.log`, `sha-N.txt`, and `source-N.lean`; matching local snapshots and the attempt inventory are under `/tmp/r0-lanemap-20261008/`. Every recorded snapshot hash was checked against its evidence. G11 has no remaining source/interface stop after the lead's PublicBase correction.

## Lead decisions after G10/G11

G10 (9c387d8bb) accepted: all five function-level bad-set and degree
obligations proved. G11's source audit (7f1d92225) is accepted and
corrects the lead's brief in three places.

1. **θ order.** The Horner fold (T:1267–1274) gives Poseidon lanes θ⁰–θ³,
   semantic packed groups 0–23 θ⁴–θ²⁷, copy residual θ²⁸. `laneOf` must
   use indices 0–3 Poseidon, 4–27 semantic, 28 copy. The brief's
   "copy first" was wrong; `lanesComp` is unchanged.
2. **Mixed groups are authorized, with the separation proved from row
   support.** Groups 0–2: scalar slots 0–11 carry
   `scheduleInitial[j] + occupancy[j]`. Every `scheduleInitial` residual
   has the factor `g2Low sel 0` (local row 0: `schedule_low_zero`), and
   every occupancy residual has the factor `rowSel b 1017` or
   `rowSel b 1018` (local rows 9 and 10 of block 63). The supports are
   disjoint, so on Boolean rows the sum vanishes everywhere iff each
   summand vanishes everywhere. G11′ proves this as
   `schedule_occupancy_separate` and then applies `pack4_eq_zero_iff`.
   Group 12 mixes path slot 48 with value slots 49–51 as distinct
   `pack4` components; `pack4_eq_zero_iff` separates them directly.
3. **Positivity is not a production lane.** Slot 94 is the research-only
   adapter already recorded under Q1 (Positive.lean:3–12). The SEM
   assembly derives `Holds` for the production families only;
   `Holds positiveFamily` enters `positivity_of_balance` as an explicit,
   separately labelled hypothesis of the proposal, never as a consequence
   of production acceptance. This is the standing Finding 1.

G11′ statement: `lanes_zero_iff_holds` as before but with the production
family list (value, occupancy, asset, schedule, path, digest,
poseidonScalar, copy via `CHolds`), without `positiveFamily`.

## Lead: SEM assembly (SemAssembly.lean)

`ProductionHolds pub lam chi t` (the eight production families, copy via
`CHolds`); `LaneInterface` (G11′'s `lanes_zero_iff_holds`, as a
parameter); `LogUpStep` (the deterministic LogUp assembly for (λ, χ)
outside a parameter bad set `BadLogUp`, to be defined from G5–G7);
`semantic_sound`: via `Zerocheck.compose`, acceptance outside the α, μ,
zc, θ and LogUp bad sets gives `ProductionHolds ∧ CopyLinkBalance`;
`semantic_positivity`: with the proposal lane `Holds positiveFamily` as a
labelled hypothesis (Finding 1), `positivity_of_balance`'s conclusion;
`ExtractionStep` (G9's statement) and `semantic_extraction`.
Attempt 619, exit 0, 1.42 s, 3326492 KiB, swap 0, 24+7 GiB. SHA-256
`6b3aa44535a857adf8829f77d0cb0f006da6fc6fa4bf195739e4c95a5887f6e5`. Axioms: standard three.

Open obligations, each a single instantiation when it lands: G11′
(`LaneInterface`), G5–G7 plus the lead LogUp assembly (`LogUpStep` and
`BadLogUp`), G8/G9 (`ExtractionStep`). After those, the FS integration:
replace `R0FS.Stmt.semantic` by the semantic acceptance predicate and add
the ledger's 302900/(P⁴−1) to the state function.

## Lead: extraction step closed; LogUp assembly objects (LogUpAssembly.lean)

G5–G9 (through f91637b81) accepted. `SemAssembly.extraction_step`
instantiates `ExtractionStep` with G9's `input_note_extracted`.
Attempt 620, exit 0, 1.42 s, 3328404 KiB, swap 0. SHA-256 `4acc8671740fe4753b3f25e08aa4b0681257637c9bd8612085970c120950dfa4`.

`LogUpAssembly.lean` fixes the LogUp step's objects for a trace t and
pub: `enabledLinks` (weight ≠ 0), `prodVal`/`consVal` (compressed
endpoint values at λ), `valueSet` D, `signedCount` m (producers minus
consumers at a value, cast to K), `prodPolys`/`consPolys` (multisets
of `compressPoly` of the tagged tuples), and `BadLogUp pub t lam chi`:
χ = 0 (empty slots carry the factor χ − 0) ∨ χ ∈ D ∨ χ a root of a
nonzero `numer D m` ∨ (S ≠ T ∧ λ a root of a nonzero coefficient of
Π(X − P) − Π(X − Q)). The ledger's activePole count becomes 273.
The chain is five named Props L1–L5; `logup_step_of` glues them, with
the Boolean-sum/Finset-sum correspondences for H1 and the inactive
helper as hypotheses (a G11′ item). Attempt 621, exit 0, 1.69 s,
3338700 KiB, swap 0. SHA-256 `79de485b1c2a3cea7f2a3290be6a9b9e82bd5f6186a843a3656b33c060ee2236`. Axioms: standard three.

G12 proves L1–L5 (statements in the file):
L1 from `copy_holds_iff` with `copy_producer_slots_nodup` /
`copy_consumer_slots_nodup` (one endpoint per slot, so each
`copyRowValues` is a single compressed value or 0 with weight 0) and
field division off poles; L2 by splitting Σ_b over active/inactive rows
and regrouping the double sum by value (`Finset.sum_fiberwise`); L3
from `numer_partial_fraction`, `numer_nonzero_bounds`,
`numer_eq_zero_imp`; L4 from `product_difference_coeff`, with
`signedCount = 0` on D giving equal value multisets (counts are < P so
the K-cast is faithful: this needs `CharP K P` with P > 136, or
char 0; state the hypothesis), and evaluation at λ commuting with the
products; L5 from `copy_tags_nodup`, `compressPoly_eq_iff` and
`copy_balance_cell`'s pattern.

Ledger update: activePole 273 (χ = 0 included), totals 3030 / 303000;
`causal_le_two_pow_neg_105` and `causal_le_v7` unchanged in force.
Attempt 622 (see evidence/out-622.log).

## Lead decision after G11′ stop: public-input base typing

Codex's counterexample is accepted: with a zero trace and
`pub.assetId = B.i`, the asset residual at row 44 is `−B.i ∉ F`, so
`pack4_eq_zero_iff` cannot be applied to groups holding asset,
withdrawal or digest targets without typing the public input. In the
source every public field is M31 (`pair_forest_semantic_terminal.rs:88–96`,
read via `lift_m31`), so the typing is a fact of the statement type.
`CoreExt.PublicBase F pub` records it (anchor, nullifier, assetId,
recipient, change, withdrawalAmount, snapshot/next frontier, nextRoot).
Appended only; no existing declaration changed. Attempt 623, exit 0,
1.45 s, 3327052 KiB, swap 0. SHA-256 `7b0a6820f1f6d446943447509edd40babf84801eb1f06aeabd868ff033d41188`.

G11′ resumes with `hpub : PublicBase F pub` as a hypothesis of
`lanes_zero_iff_holds`; `SemAssembly.LaneInterface` gains the same
hypothesis at instantiation time (it is a parameter there, unchanged).
In the FS integration, `PublicBase` is discharged from the statement's
M31 public fields, not assumed of the prover.

## Lead decision after G12 L1 stop: poles over all links

Accepted: `copy_logup_residual` (logup.rs:228–252) multiplies all four
slot denominators whether or not the slot's link is enabled, so a disabled
endpoint value equal to χ zeroes the row residual for any H1 (registry
index 3 under withdrawal, rows 443/448). `LogUpAssembly` now has
`poleSet t lam` over all 136 links' producer and consumer values;
`BadLogUp` and L1 use `chi ∉ poleSet`, L2/L3 keep `valueSet` (enabled
values), and `valueSet_subset_poleSet` bridges them in the glue. The
pole count is unchanged (≤ 272 values, 273 with χ = 0); the ledger stands.
Attempt 624 green with an unused-binder lint; 625 after dropping the
binder: exit 0 (see evidence/out-625.log). SHA-256 `a6169f9bfddbc51f56f741bd61991cfc1336d326963a9fa02c5c7751891d6bdc`.

Correction: 714de1bbf was committed on the runner's shell exit, not the
Lean exit; attempt 625 had exit 1 (a substitution error in the glue's
lemma application). Attempt 626 on the corrected file: exit 0, 1.81 s,
3339780 KiB, swap 0, 24+7 GiB, no warnings. SHA-256 `1f2aa23fce266027f8d0c4af639d0d9c98439500ab4d07c984afa64a8ac5f157`.
`logup_step_of` axioms: propext, Classical.choice, Quot.sound.

## G12: LogUp chain source/interface review

Started against `e1b73deae8e8f00a153d04ca8ed8f44478da77c0`; resumed after `ce62ca555` with the corrected `poleSet`. No existing Lean file was edited and no `LogUpChain.lean` theorem has been claimed.

### L1 denominator finding, accepted and resolved by the lead

The original L1 excluded only enabled endpoint values. The literal Copy fold accumulates compressed values even when their weights are zero (`Copy.lean:98–108,447–458`; pinned `pair_forest_copy_terminal.rs:424–449,943–970`). Registry index 3, tag 1124073475, has weight kind 1 and active endpoint rows 443/448 (`CopyConstants.lean:142–147`); under withdrawal its weight is zero but its values still enter the slot denominators. Excluding only `valueSet` therefore did not justify dividing all four factors. The lead's `poleSet t lam` now includes both endpoints of every link, with `valueSet_subset_poleSet` for the enabled-value steps. The corrected L1 and glue were reviewed; this finding is resolved by commits `714de1bbf` and `ce62ca555`, not by changing the literal Copy port.

### Remaining L5 tag-cast gap

`LogUpL5` remains stated over an arbitrary `Field K` (`LogUpAssembly.lean:20,113–115`). The requested route uses distinct tags to identify the same enabled link on both sides of equal polynomial multisets. However, `copy_tags_indexed` and `copy_tags_nodup` prove distinctness in `Nat` (`CopyRegistry.lean:245–286`), while `copyEndpointTuple` casts each tag to `K` (`Copy.lean:79–81`). `compressPoly_eq_iff` recovers equality of pairs in `K × (Fin 16 → K)` (`LogUpCompress.lean:55–66`); it does not recover equality of the original Nat tags.

In characteristic 2, distinct registry tags 1124073472 and 1124073474 both cast to zero. These are always-enabled indices 0 and 2, both with the full-state pattern (`CopyConstants.lean:143,145`). Thus the Nat-nodup theorem does not provide the field-tag injectivity required by L5's stated proof route. This is a source/interface finding, not a newly kernel-checked counterexample to the full L5 proposition. The user authorized `[CharP K (2^31 - 1)]` specifically for `logupL4`; no corresponding premise was added to `logupL5` here.

Smallest proposed repair, not enacted: require injectivity of the tag casts on the enabled registry, or authorize an appropriate characteristic hypothesis for `logupL5` too. The M31 characteristic instance already requested for L4 suffices, using `copy_tags_indexed` and the tag interval bounds. The frozen definitions and statements were not changed. G12 stops on this remaining missing bridge as instructed; G11 proceeds independently.

The L3 route was independently checked against `numer_partial_fraction` and `numer_eq_zero_imp`; L4's route is available with its authorized characteristic hypothesis and the existing 136-link multiplicity bound. These are feasibility reviews, not completed new Lean proofs.

### Dependency build evidence

The requested focused rebuild used `run2.sh 1800 R0P/LogUpAssembly 7000 7` on the pinned host/cache after synchronizing the corrected lead source. Scope/Lean exit 0, time exit 0, wall 1.62 seconds, peak RSS 3,340,220 KiB, swaps 0; reservation 24 + 7 GiB, MemoryHigh 5 GiB, MemoryMax 7 GiB, MemorySwapMax 0. SHA-256 `1f2aa23fce266027f8d0c4af639d0d9c98439500ab4d07c984afa64a8ac5f157`. The existing `logup_step_of` audit reports only `propext`, `Classical.choice`, and `Quot.sound`; no warnings. This is a dependency check, not evidence for L1–L5. No G12 development failure or new theorem audit occurred; the next unused development attempt is 1801. Raw host evidence is `evidence/out-1800.log`, `time-1800.log`, `sha-1800.txt`, and `source-1800.lean`; local evidence and source hashes are under `/tmp/r0-logupchain-20261008/`.

### Continuation G12 — deterministic chain completed

Resumed after the lead's `e91642e9c` decision, on source revision `0773ff34e9f2d045c48780932e3cab7f9a9f8594` (the already completed G11′ continuation). `LogUpChain.lean` imports the corrected `R0P.LogUpAssembly` and proves the five unchanged Props as `logupL1` through `logupL5`. L1–L3 require only `Field K`. L4 and L5 both take `(P : Nat) [CharP K P] (hP : P = 2 ^ 31 - 1)` exactly as authorized; their fixed `LogUpL4`/`LogUpL5` targets are unchanged. This resolves the historical L5 stop above. No existing Lean file was edited.

L1 uses the producer/consumer slot Nodup lemmas to show each slot contains at most one registry endpoint. Its denominator proof uses all-link `poleSet`, including disabled endpoints, with `chi ≠ 0` for empty slots. The five weight kinds are proved to give 0 or 1 using a generic Nat low-bit lemma; disabled slots contribute zero and enabled slots contribute a unit reciprocal. The literal row identity is divided only after proving all four denominators nonzero. L2 splits the total helper sum into active and inactive parts, substitutes L1's row form and regroups symbolic list sums first by row and then by compressed value. It retains the fixed off-`valueSet` premise and adds no premise.

L2 required an endpoint-support fact absent from the existing registry API: every producer and consumer endpoint row is active. The user explicitly authorized a bounded endpoint/mask check in `LogUpChain` using the three existing registry blocks. `copyLinks_endpoints_active` supplies that fact. The 14-link and 4-link blocks are checked separately; the 118-link block is partitioned into 20/20/20/20/20/18 records by generic `take`/`drop` lemmas. Each Boolean check reads only those endpoint rows' mask bits. The unsplit final block hit the default recursion limit in 1810; the replacement splits the computation without changing a cap or option. The complete focused coverage check 1812 costs 2.42 seconds, 3,347,272 KiB peak RSS and zero swaps. No trace, row range, field universe, permutation or unrelated constant table is evaluated.

L3 uses the partial-fraction identity, its nonzero denominator, and the excluded nonzero-numerator root event to obtain `numer = 0`, then `numer_eq_zero_imp`. L4 converts zero signed counts to equal value multisets using counts bounded by 136 below P, maps products of `X - C q` through evaluation at lambda, and applies `product_difference_coeff`. L5 combines `compressPoly_eq_iff` with the shared tag and registry Nat-tag Nodup; `copy_tags_indexed` puts every tag below P, and `CharP.natCast_eq_natCast` recovers Nat equality from the cast equality. Neither step evaluates the registry. No probability claim is made.

The coordinator reviewed the combined source and the source-facing Copy/pole interfaces; independent mechanical reviews also checked L1 and L3–L5. Final source SHA-256: `516f9d6a2b730ab1c6a8c5a9294b132672b0f7043d83f16046ef6bd19b05ed25`. Coordinator check 1899 compiled the actual frozen 895-line file with all five public chain lemmas. Every theorem and definition has an audit: 57 outputs, only `propext`, `Classical.choice` (printed as `choice` by Lean) and `Quot.sound`, no warnings, no errors. Scope/Lean exit 0 and time exit 0, wall 4.30 seconds, peak RSS 3,387,000 KiB, swaps 0.

All jobs used the pinned Lean 4.32.0/cache on `dombarker@100.108.41.90`, workspace `/home/dombarker/project-offloads/aspis-fs-generic-20261006/`, `run2.sh N R0P/LogUpChain 7000 7` except dependency 1800 (`R0P/LogUpAssembly`). Reservations were 24 + 7 GiB, MemoryHigh 5 GiB, MemoryMax 7 GiB, MemorySwapMax 0. One G12 job ran at a time. The table records actual Lean and scope/time exits; the outer runner shell's success was not used as proof evidence. No unchanged failing source was rerun.

| Attempt | SHA-256 | Lean / time exit | Wall s | RSS KiB | Swaps | Result |
|---|---|---:|---:|---:|---:|---|
| 1800 | `1f2aa23fce266027f8d0c4af639d0d9c98439500ab4d07c984afa64a8ac5f157` | 0 / 0 | 1.62 | 3,340,220 | 0 | Corrected LogUpAssembly dependency, green. |
| 1801 | `84fa0a5f7094afb546e9fa05c83f37ebcbd17ab3ff175aee498b33e4df909a6f` | 1 / 1 | 1.79 | 3,329,668 | 0 | L3–L5: List/Multiset count normalization and implicit characteristic inference failed. |
| 1802 | `82406a0757c07ef5430183991215bdbe3599e6b84e7490c163c6638d10e668a3` | 0 / 0 | 1.82 | 3,344,560 | 0 | L3–L5 green; 11 audits, no warnings. |
| 1803 | `2f26c555c2c7001990685931c1c753f86242ec84a3ee287637a22f1be948f594` | 1 / 1 | 2.22 | 3,340,440 | 0 | L1: syntax, helper-name, finite-slot and list proof elaboration failures. |
| 1804 | `bd5704809d2fffc9f5d8df99f3aa086ac8b88c4fb39e954b91e010b1a24b49e1` | 1 / 1 | 1.51 | 3,325,908 | 0 | L2: implicit mem_cons arguments and fiber rewrite elaboration failures. |
| 1805 | `19b77dc05f31aef927ba95ba48ed89fa4982ed1e9bbd9e7134ffe23ea7a18409` | 1 / 1 | 2.44 | 3,350,012 | 0 | L1: slot associativity, generalized-list names, filter membership and Boolean filter ordering failures. |
| 1806 | `2f85dcd277c9b82c6382baa1f981b3ba1be551dfff688c0b8fee8c1bdcad36d1` | 1 / 1 | 1.58 | 3,325,568 | 0 | L2: concrete/Classical Fin equality instance mismatch in filter rewrite. |
| 1807 | `7bbe349947d2d9a799573cb737c2e864a3b41ecb8527d2ee1e1876c7d128e968` | 1 / 1 | 2.33 | 3,349,728 | 0 | L1: filter membership projected before applying mem_filter; two unused simp warnings. |
| 1808 | `f157ea27226f8680f259c2ac9532fdf14dbf1aff82b01306d74e5361ff3c8745` | 0 / 0 | 1.59 | 3,335,272 | 0 | L2 generic assembly helper green; 6 audits, no warnings. |
| 1809 | `ed2eb3d991dc109c48484496f6df3b487b31a831c950952e2f6e0364def4f204` | 0 / 0 | 2.45 | 3,365,448 | 0 | L1 green; 24 audits, no warnings. |
| 1810 | `9a70e32927dadff53090cb6f1bee3b9df6411a9162c5fd3ed4ad47f573e93ca8` | 1 / 1 | 1.78 | 3,340,020 | 0 | Coverage: empty-list goal, append association, and default recursion depth on the 118-record block. |
| 1811 | `aea3b45e433237cbfbc28c0cce92cf19fde43f4aec4d48756c34a505ff2cc1a1` | 1 / 1 | 2.31 | 3,331,732 | 0 | All bounded record checks green; generic take/drop glue failed after broad simp folded it back. |
| 1812 | `5c10c8166ec8aa4a3bd520dcf78ba31a3d2793f692dd4f76468c4752ea1cd49e` | 0 / 0 | 2.42 | 3,347,272 | 0 | Coverage green; 15 audits, no warnings. |
| 1899 | `516f9d6a2b730ab1c6a8c5a9294b132672b0f7043d83f16046ef6bd19b05ed25` | 0 / 0 | 4.30 | 3,387,000 | 0 | Frozen combined coordinator check green; 57 audits, no warnings. |

Failed development logs include Lean's error-recovery `sorryAx` and were rejected; none is present in a green audit or the final source. Raw evidence and exact source snapshots are retained on the host as `evidence/out-N.log`, `time-N.log`, `sha-N.txt`, `source-N.lean`, and copied locally under `/tmp/r0-logupchain-20261008/evidence/`; every copied snapshot matches its recorded SHA. Final static review found no `sorry`, `axiom`, `admit`, `native_decide`, recursion/heartbeat option change, or prohibited normalization. The previous pole and tag-cast findings are resolved by the lead's corrections; the endpoint-support bridge is proved with the user's bounded-check authorization. G12 has no remaining stop.

### Continuation G12′ — leading-coefficient L4

After lead commit `63ffcd341`, only the proof of `logupL4` was changed in `LogUpChain.lean`; the signatures, L1–L3, L5 and all helpers are byte-for-byte unchanged. Equal signed counts still give equal value multisets at lambda under the authorized `(P : Nat) [CharP K P] (hP : P = 2 ^ 31 - 1)`. Mapping the outer product difference through `evalRingHom lam` therefore gives zero. Taking its coefficient at the difference's `natDegree` shows that its leading coefficient evaluates to zero. The proof also derives nonzero product difference from `product_difference_coeff`'s monic-root-product inequality and derives its nonzero leading coefficient. It contradicts exactly the lead's new leading-coefficient bad event; no existential coefficient branch remains in L4.

The coordinator reviewed the isolated proof diff and compiled the frozen source, then rebuilt the unchanged lead `SemClosed.lean` in the same objects directory. Attempt 1813 failed because the final constructor still used the previous existential shape; 1814 corrected that application and passed. All jobs used pinned Lean 4.32.0, `run2.sh N R0P/<target> 7000 7`, reservation 24 + 7 GiB, MemoryHigh 5 GiB, MemoryMax 7 GiB, MemorySwapMax 0, one G12 job at a time. No unchanged failure was rerun.

| Attempt | Target | SHA-256 | Lean / time exit | Wall s | RSS KiB | Swaps | Audits |
|---|---|---|---:|---:|---:|---:|---|
| 1813 | LogUpChain | `ab98502d5ee3cd44e7c7180d4e8145e33f5d4e571811f63012dd201354bd7a36` | 1 / 1 | 4.33 | 3,365,344 | 0 | Rejected error-recovery L4 audit; old constructor shape. |
| 1814 | LogUpChain | `a9b0e52dd73026f356c16237d4b29527a70a479fc14cb0d59c178e1d94ff1fb6` | 0 / 0 | 4.24 | 3,386,880 | 0 | 57 permitted audits, no warnings. |
| 1815 | SemClosed | `05ed018167483ebe6cb14b4064d2dd7aa4a4ec8da950592bc88ee7ab4f30f7cf` | 0 / 0 | 1.42 | 3,332,880 | 0 | Both closed soundness/extraction audits permitted, no warnings. |

The green audits contain only `propext`, `Classical.choice`/Lean's printed `choice`, and `Quot.sound`. The final LogUpChain source exactly matches attempt 1814. `SemClosed` source was synchronized but not edited; its exit is **0**. Raw host evidence and exact snapshots are `evidence/out-N.log`, `time-N.log`, `sha-N.txt`, `source-N.lean`; verified copies are under `/tmp/r0-logupchain-20261008/evidence/`. No forbidden proof terms, cap changes or table/trace/row evaluation were introduced. G12′ is complete; G13′ proceeds separately with the corrected interfaces.

## Lead decision after G12 L5 stop: characteristic premise for L4 and L5

Accepted: `copy_tags_nodup` is Nat-level; in characteristic 2 the casts of
tags 1124073472 and 1124073474 coincide. The SEM field is QM31, of
characteristic P = 2^31 − 1, and every registry tag is < P
(`copy_tags_indexed`: 1124073472 + i, i < 136), so under `[CharP K P]` the
cast is injective on the registry (`CharP.natCast_eq_natCast` with both
tags < P). `logupL4` and `logupL5` both take `(P : Nat) [CharP K P]
(hP : P = 2 ^ 31 - 1)`, in the form already used by `positivity_of_balance`;
no definition or L-statement in `LogUpAssembly.lean` changes, and
`logup_step_of` is applied with those instances in scope. The glue's
hypotheses `h4`, `h5` are quantified so this is a plain instantiation.

## Lead: closed SEM theorem (SemClosed.lean)

G11′ (0773ff34e) and G12 (f026c447f) accepted. `semantic_sound_closed`
instantiates `semantic_sound` with `lanes_zero_iff_holds` (lane map,
under `BaseTyped F t`, `PublicBase F pub`, `B : PackBasis F`) and
`logup_step_of` with `logupL1`–`logupL5` (characteristic P for L4/L5),
with `lane_h1_sum`/`lane_inactive_sum` for the helper sums.

Statement: for a trace t and public input pub, if the sumcheck's Boolean
row values are the terminal's `eq(zc,b)·Σθⁱ laneᵢ + μ·H1 + μ²(1−active)H1`,
the virtual polynomial has individual degree ≤ 27, the verifier accepts
claim 0, and (α, μ, zc, θ) and (λ, χ) are outside the ledger's bad sets,
then every production family holds on t and the copy links balance.
`semantic_extraction_closed` then gives `InputNoteExtracted pub t`; with
the proposal's positivity lane, `semantic_positivity` gives the integer
split. Attempt 627, exit 0, 1.43 s, 3332580 KiB, swap 0, 24+7 GiB.
SHA-256 `0ff01dadc3fb6a33a0d5692e5825c4dbbb9dc1b62700f371be3e15168f99ab1a`. Axioms: propext, Classical.choice, Quot.sound.

This closes SEM for one candidate at the deterministic level, with the
bad-set masses in `SemLedger` (303000/(P⁴−1) ≤ 2⁻¹⁰⁵) and their per-branch
cardinalities in `SemBadSets`/`LogUpChain`. Remaining: the FS
integration (replace `R0FS.Stmt.semantic`; discharge `PublicBase` from the
M31 public fields and `BaseTyped` from `Stmt.base`; union over the ≤ 100
candidates; add the ledger to the state function) and the deferred
Rust-to-model refinement of the raw-limb Poseidon implementation.

## Lead: FS integration design (semantic rounds)

Challenge order (aspis-prover v6_onefold_prover.rs:596–600, 604–612;
aspis-core state_only_sumcheck.rs:96–105, 241): trace commitment →
λ → χ → H1 commitment → θ → zc₁…zc₁₀ → μ → ten sumcheck rounds α₁…α₁₀
(each after the round polynomial) → point claims → z₀, z₁ → opening
layer. μ is sampled last among the batching challenges, so `BadMu`'s
coefficients (mle(comp θ)(zc), ΣH1, Σinact) are fixed before it, as
`Zerocheck.compose` assumes.

Instantiation of `R0C.SemStatement.SourceData` (B2) for the pair forest:
`semanticRounds = 24` scalar rounds in this order, with `semanticBad`
quantified over the candidate list `Λ(W)` of the committed words
(`Lambda_card ≤ 100`), and per-round budgets (over |K|, K = QM31):

| round | challenge | bad set (per candidate t) | per-trace | ×100 |
|---|---|---|---:|---:|
| 0 | λ | coefficient-root branch of `BadLogUp` | 2176 | 217600 |
| 1 | χ | χ = 0 ∨ χ ∈ poleSet ∨ numer root | 544 | 54400 |
| 2 | θ | `BadTheta (laneOf t) θ` | 28 | 2800 |
| 3–12 | zc_j | partial `mle` nonzero in z_j and z_j its root | 1 each | 100 each |
| 13 | μ | `BadMu` | 2 | 200 |
| 14–23 | α_j | round j's `polys j − honest j ≠ 0` with root α_j | 27 each | 2700 each |
| | | total | 3030 | 303000 |

The zc and α rounds use the round-by-round forms already proved in
`SemBadSets` (`mle_bad_card`'s induction step is the per-coordinate
statement; `adaptive_strategy_bad_card`/`badAlpha_strategy` the
per-round sumcheck statement). The doomed state after the semantic rounds
is "no candidate t ∈ Λ(W) satisfies `ProductionHolds ∧ CopyLinkBalance`
for the sampled (λ, χ) and no semantic round was bad"; `semantic_sound_closed`
is the D3 content (acceptance of a doomed complete prefix is impossible),
and the ×100 union over Λ(W) is the D2 content per round.
`paymentWitness x w` := `InputNoteExtracted` for the extracted candidate,
with the proposal positivity kept outside (Finding 1). `BaseTyped` is
discharged from `Stmt.base` (C1 lanes in M31) and `PublicBase` from the
M31 public fields; `IndDeg 27 10 G` from `SemBadSets.mlDeg_*` applied to
the terminal's polynomial structure; `hG` from the ports' Boolean-row
evaluation (`rowOpenings`/`rowSel`).

Remaining jobs, in order: (G13) `SemRounds.lean`: the 24-round
classifier, the per-round doomed predicate, and the deterministic D1/D3
lemmas from `semantic_sound_closed`; (G14) per-round density D2 for the
24 rounds from the card lemmas, under the duplex sampler law already
used in R0C/V3 (`DuplexQ`); (lead) the combined protocol's Theorem-4
instance with budget `rowBudget` replaced by the table above and the
opening rows unchanged, giving the end-to-end bound
`Q_tot · max_i ε_i + 2Q_tot²/2^256` with the semantic rows ≤ 2⁻¹⁰⁵ each
and the q22 row 2⁻¹⁰⁵·¹⁴ still the maximum.

## G13: Semantic-round interface stop

Started at lead design commit `fa6bb2a22eff6ae877bc1954cd4de8ba52951666`, after fetch/fast-forward verification. The closed theorem and cached sources were inspected before defining the requested 24-round classifier. The fixed coverage target cannot be obtained from the prescribed local alpha events: its `¬ BadAlpha 27 10 α` conclusion is impossible over every field. Work stopped at that statement as instructed. `SemRounds.lean` contains only four checked finding lemmas; no `semRoundBad`, `semRoundBad_card`, `semRounds_cover`, or `semantic_sound_rounds` is claimed. No existing Lean file was edited.

### Alpha quantifier finding: checked obstruction

`Zerocheck.lean:88–89` defines `BadAlpha d n α` as `∃ i, ∃ p : K[X], p ≠ 0 ∧ p.natDegree ≤ d ∧ p.eval (α i) = 0`. The existential polynomial is unrestricted and can depend on the sampled coordinate. For any nonempty challenge vector and `1 ≤ d`, choose `i = 0` and `p = X - C (α i)`. Its coefficient at 1 is 1, its degree is at most 1, and its evaluation at that coordinate is zero. Thus every challenge vector satisfies the existing event; this holds over finite fields too.

The new file proves `badAlpha_all_rounds`, specializes it to `badAlpha_27_10`, and proves `badAlpha_27_10_negation_impossible`. `equal_round_polynomials_do_not_exclude_badAlpha` also proves that when every prover round polynomial equals its honest polynomial, all prescribed nonzero-difference root events are false while the existing `BadAlpha` is still true. These are symbolic polynomial proofs; the only concrete decisions are the small Nat inequalities `0 < 10` and `1 ≤ 27`.

The impossible negation is required by `Zerocheck.compose` at `Zerocheck.lean:109`, `semantic_sound` at `SemAssembly.lean:57`, and `semantic_sound_closed`/its extraction wrapper at `SemClosed.lean:33,62`. Those conditional theorems remain valid Lean theorems, but their current alpha premise is uninhabited. In contrast, `SemBadSets.badAlphaStrategy` (`SemBadSets.lean:929–931`) is the event that the fixed adaptive strategy is accepted with a false initial claim; `adaptive_strategy_bad_card` (`:991–996`) and `badAlpha_strategy` (`:1147–1154`) bound that strategy-specific event. They do not bound or identify the unrestricted `BadAlpha` event.

Smallest required interface repair, not enacted: the composition/closed-theorem alpha premise must use the actual prefix-fixed prover/honest difference event (with the verified round degree bound), or consume `bsum 10 G = 0` obtained from its avoidance and acceptance. The corresponding G13 coverage conclusion must target that event rather than `¬ BadAlpha`. This requires a lead decision and edits outside G13's allowed files. No root-count claim for the existing universal event is made.

### Lambda coefficient selection: additional quantifier gap

The exact lambda branch of `BadLogUp` (`LogUpAssembly.lean:64–72`, repeated in `LogUpL4` at `:104–111`) is `S ≠ T ∧ ∃ k, (Q.coeff k) ≠ 0 ∧ (Q.coeff k).eval lam = 0`, where `Q` is the difference of the producer and consumer outer-polynomial products. It is a union over all nonzero coefficient root sets, with the witness allowed to vary with lambda. `product_difference_coeff` (`SemBadSets.lean:227–235`) supplies one nonzero coefficient of degree at most `16 * max S.card T.card`; a root bound for that one coefficient does not establish the requested 2176 bound for the existing existential union.

This is an additional missing quantifier bridge, not a checked counterexample to the concrete registry's 2176 bound. To use the cited single-polynomial root-count route, a nonzero coefficient must be selected from the fixed candidate before lambda is sampled and used consistently in the bad-set and LogUp interfaces; alternatively, the full union needs its own proof of the stated bound. Neither change was made. The alpha obstruction already requires stopping, so no table, trace, candidate registry, or field universe was evaluated to explore the lambda issue.

### Focused evidence

Coordinator check `run2.sh 1900 R0P/SemRounds 7000 7` on the pinned Lean 4.32.0 host/cache passed: actual Lean/scope exit 0, time exit 0, wall 1.43 seconds, peak RSS 3,336,204 KiB, swaps 0. Reservation 24 + 7 GiB, MemoryHigh 5 GiB, MemoryMax 7 GiB, MemorySwapMax 0. All four theorem audits contain only `propext`, `Classical.choice`, `Quot.sound`; no warnings or errors. No failed G13 attempt or unchanged rerun occurred. The exact frozen 70-line file has SHA-256 `82136911d0a0ce31c21a8c3d7a39dfa04277905fbf40d573fb90da0318b3bb5b`.

The host `SemClosed` source matches current repository SHA-256 `0ff01dadc3fb6a33a0d5692e5825c4dbbb9dc1b62700f371be3e15168f99ab1a`; its existing compiled object and direct dependency objects were reused. `SemBadSets` source SHA-256 is `b74e1d7adfaaf6ad0c4973b96461b6359d23b62d6cadb6e2983646d3e5b40b5d`. No dependency rebuild was needed. Raw host evidence is `evidence/out-1900.log`, `time-1900.log`, `sha-1900.txt`, `source-1900.lean`; verified local copies are under `/tmp/r0-semrounds-20261008/evidence/`. The coordinator reviewed the finding proof and fixed interfaces; independent source reviews confirmed the alpha and lambda quantifier differences. No forbidden proof terms/options, probability claims, or requested completion claim was introduced.

### Continuation G13′ — completed literal semantic rounds

Resumed after the lead's `63ffcd341` corrections and `e5d8519bb` degree-premise decision, on source revision `de0fe30a0`. The accepted earlier counterexamples remain recorded above and in commit `4e8c68399`; their obsolete-interface proof file is replaced by the completed round module.

`SemRounds.lean` now defines `semRoundBad` on `Fin 24`, an earlier-challenge prefix, a candidate trace/public input/packing basis, and the current challenge. Its order is λ (0), χ (1), θ (2), ten zerocheck coordinates (3–12), μ (13), and ten alpha challenges (14–23). This matches `v6_onefold_prover.rs:596–600,604–612` and `state_only_sumcheck.rs:96–105,241` at the recorded Rust inspection pin. The virtual polynomial depends on the first fourteen challenges; each strategy polynomial depends on those and its strictly earlier alpha prefix. No branch reads the current challenge from its prefix.

The module proves:

- `semRoundBad_card`: per-candidate bounds 2176, 544, 28, 1, 2, 27 in that order. The alpha case alone uses `semRoundDegreeChecked`, precisely the already-checked `(polys j).natDegree ≤ 27`. This premise is absent from the round predicate, recursive bridge, coverage theorem, and semantic implication. `accept_polys_degree` derives every such observed degree bound from acceptance.
- `badAlpha_iff_exists_round`: the literal recursive `Sumcheck.badAlpha` is exactly the union of its prefix-fixed round disjuncts. `badAlphaStrategy_imp_exists_round` connects an accepted false adaptive claim via `Sumcheck.sound`; it makes no converse assertion about accepted false claims.
- `zc_rounds_iff`: a nonzero Boolean function has zero MLE at the full point iff one prefix restriction first collapses to the zero Boolean-tail function. Symbolic dimension induction and one nonzero Boolean witness give the per-coordinate bound 1.
- `semRounds_cover`: absence of all round events excludes the five joint events consumed by `semantic_sound_closed`.
- `semantic_sound_rounds`: the closed semantic implication with the five exclusions replaced by absence of bad rounds, retaining the same characteristic, base typing, public typing, terminal identity, degree, and acceptance premises.

The λ proof uses the fixed leading coefficient, a symbolic multiset-product coefficient-degree induction, the existing registry length bound, and nonzero univariate root counting. The χ proof counts at most 272 poles, at most 271 numerator roots, and zero. It uses all-link `poleSet` and enabled-link `valueSet` exactly as fixed. No list/trace/row/universe/table/permutation evaluation, source reinterpretation, probability claim, cap change, or dependency rebuild was introduced.

All development used the pinned Lean 4.32.0 build host/cache and `run2.sh N R0P/SemRounds 7000 7`: MemoryHigh 5 GiB, MemoryMax 7 GiB, MemorySwapMax 0. Reservations were 26 + 7 GiB for 1901–1902 and 24 + 7 GiB thereafter. Each row below records actual Lean/scope exits (not the runner shell status); swaps were zero throughout. Every failed source was changed before retry. Components were checked separately before the combined bridge; 1999 is the reserved final coordinator audit of the frozen repository file.

| Attempt | SHA-256 | Lean / scope exit | Wall | Peak RSS KiB | Result |
|---:|---|---:|---:|---:|---|
| 1901 | `6655d5c320faeabf786671d34564e16a149a7bdd11a312bfd75dd5314a6b32aa` | 1 / 1 | 0:00.91 | 2,084,700 | Alpha parser rejected reserved `prefix`; cascading declarations. |
| 1902 | `21981a885bef11802f3d711122bc6ad58286a9dd81e6e96cb4ed30f0c91ad318` | 1 / 1 | 0:00.98 | 2,091,100 | Alpha Fin projection/definitional equality and empty-filter lemma. |
| 1903 | `d54697af34e763e4eba59d023d1377d7d3437af138a9b56291c6544a8dbb4812` | 1 / 1 | 0:01.30 | 2,098,728 | ZC dependent recursion, missing tactics/instances and MLE rewrites. |
| 1904 | `3db3877888b75317f53ec14101e4d000745196faf90c9c4364e010a89cb2bc91` | 1 / 1 | 0:02.06 | 3,331,356 | LogUp classical/noncomputable declarations, coefficient-degree and union-bound elaboration. |
| 1905 | `c9a4ce4dc7b7edc00a5a5f9d96bfefa1520361a46999e16c1731de87a3bfa29d` | 0 / 0 | 0:00.98 | 2,101,732 | Alpha helpers green; 7 audits, no warnings. |
| 1906 | `37486c176d8e79d8b9b77a0ca7ca218cd90eea22e23a8d8d0be1a6dfd4591934` | 1 / 1 | 0:01.31 | 2,105,020 | ZC recursion pattern, instances, witness rewrites and card binder order. |
| 1907 | `a05f48af6b534894d7f07cde1435d6333f68d25d829775014046a1f8338cc924` | 1 / 1 | 0:01.75 | 3,334,200 | LogUp noncomputable instances and wrong outer-union bound; default recursion limit reached, no limit changed. |
| 1908 | `1980ee6367a7de8b2d50a4a7afb8dc414dad04f4dbbb257fe1cd90a1043ef963` | 1 / 1 | 0:01.39 | 2,104,116 | ZC zero-equation arity, zero rewrite, typed event projection and scope closure. |
| 1909 | `9435b787adc24049d9434e3fdcd7b26556c23a0d69726f7b043839bb306c4c4c` | 0 / 0 | 0:01.81 | 3,349,224 | LogUp bounds green; 14 audits, no warnings. |
| 1910 | `9a34d1267f9f991f770f3870064c82f1c8b163b7e2e813d0eff18ec470735848` | 0 / 0 | 0:01.03 | 2,101,968 | Alpha acceptance/adaptive bridge added; 9 audits, no warnings. |
| 1911 | `483a57a6ea607cfc231c6ae1105a4c8658fb5cc419551ff18434e5b0a8c7f3d4` | 1 / 1 | 0:01.54 | 2,106,456 | ZC last `Fin.cases 0` simplification mismatch. |
| 1912 | `b32ebb842b2ba7bc85f5fe7dbef7267aa079876c238805146989b2e5edfbfcfe` | 0 / 0 | 0:01.57 | 2,117,780 | ZC green; 14 audits, no warnings. |
| 1913 | `17666f971023f22a864ba837863a7c5f2b0d7ec5d7ca8502e94831f2213a9490` | 1 / 1 | 0:03.97 | 3,370,480 | Combined cardinality theorem green; four prefix-cast/dependent-index errors in RoundCover. |
| 1914 | `564b9026233a36736f524407f357b44e173173139e52b9c4c6effbd88335bfd4` | 0 / 0 | 0:04.02 | 3,395,856 | Full module green; 55 audits, no warnings. |
| 1999 | `564b9026233a36736f524407f357b44e173173139e52b9c4c6effbd88335bfd4` | 0 / 0 | 0:04.02 | 3,396,240 | Final coordinator audit green; 55 audits, no warnings. |

Final SHA-256: `564b9026233a36736f524407f357b44e173173139e52b9c4c6effbd88335bfd4`. Attempts 1914 and 1999 match that frozen source. The final 55 declaration audits (including all private helpers) contain only `propext`, `Classical.choice`/Lean's printed `choice`, and `Quot.sound`, or no axioms. Final actual Lean and scope exits are 0, wall 4.02 s, peak RSS 3,396,240 KiB, swaps 0; no warnings or errors.

Raw host artifacts are `evidence/out-N.log`, `time-N.log`, `sha-N.txt`, and `source-N.lean`; verified copies are under `/tmp/r0-semrounds-20261008/evidence/`. The coordinator reviewed the exact events, source challenge order, prefix causality, all three component proofs, the final diff, and final build evidence. G13′ is complete. Its earlier λ/alpha interface stops are resolved by the lead's changes; the alpha count remains conditional only on the authorized pre-challenge degree check. No remaining G13 finding.

## Lead corrections after G13 stop (badAlpha, λ coefficient)

Both G13 findings (4e8c68399) are accepted; both were lead definition
errors.

1. `BadAlpha` as "∃ nonzero degree-≤d polynomial with root α_i" is
   satisfied by `X − C (α i)`, so `compose`, `semantic_sound` and
   `semantic_sound_closed` carried an unsatisfiable hypothesis. Replaced
   by `Sumcheck.badAlpha d n G polys α`, recursive on rounds: at some
   round the prover's `polys 0` differs from an honest polynomial `h`
   (degree ≤ d, `h.eval x = bsum n (G ∘ Fin.cons x)`) and `α 0` is a root
   of `polys 0 − h`; otherwise recurse on the prefix-restricted G.
   `sound` now concludes `badAlpha` with the same proof (its witness was
   already `polys 0 − h`). `Zerocheck.BadAlpha` is an abbreviation;
   `compose`, `semantic_sound`, `semantic_sound_closed` take
   `¬ BadAlpha 27 10 G polys α`. For a fixed prefix the round event is the
   root set of one nonzero degree-≤27 polynomial, so the per-round count
   27 stands; G10's `badAlpha_strategy` is the adaptive-prefix form and
   its bridge to `badAlpha` is a G13′ item.
2. The λ branch quantified over every coefficient of
   `Π(X − P) − Π(X − Q)`; the ledger's 2176 is for one coefficient.
   `LogUpAssembly.productDifference` names the difference and the branch
   is now `productDifference.leadingCoeff.eval lam = 0` (nonzero iff
   S ≠ T; λ-degree ≤ 16·136). `LogUpL4` changed accordingly;
   `logupL4` must be re-proved (G12′), after which `SemClosed` recompiles
   unchanged.

Attempts 628 Sumcheck, 629 Zerocheck, 630 SemAssembly, 631 LogUpAssembly:
all exit 0 (0.91/1.35/1.42/1.51 s; ≤ 3340248 KiB; swap 0). `SemClosed`
is pending `LogUpChain`.

## Lead: B2 instance, part 1 (SemSource.lean)

`SemSource.lean` imports `R0C.SemStatement` (the B2 skeleton of the
close job) with K = E. `Context K` = pair-forest public input plus the
committed words; `paymentWitness x t := InputNoteExtracted x.pub t`;
`d1_of_sourceData`: FS2.D1 for every semantic `SourceData` (no witness ⇒
doomed at the empty prefix, since `hitFrom [] [] = False`). Attempts
632–634 were namespace lookups (`InitialWord`, `Table`) and the
classical `dite` split; 635 exit 0, 2.95 s, 6795812 KiB (R0C imports),
swap 0, 24+7 GiB. SHA-256 `e79ce46d3ce2dc99e65aa99c78581f5069c66eec3dba4dae0dce09ec86f7a024`. Axioms: standard three.

Remaining for the B2 instance: `semanticBad` from G13′'s
`semRoundBad` (quantified over `Lambda x.W`), `openingView`
(construct the R0FS `Stmt` from the semantic transcript's point claims
and z₀, z₁), `decision`; then D3 from `semantic_sound_closed` and D2
per round from `semRoundBad_card` under the duplex sampler law.

## Lead decision: degree premise for the α-round count (G13′)

`badAlpha` bounds the honest polynomial's degree but not the prover's.
`accept` checks `(polys j).natDegree ≤ 27` at round j, before α_j is
sampled, so a transcript violating it is rejected independently of α_j.
The α-round cardinality lemma may therefore take `(polys j).natDegree ≤ 27`
as a premise (counting only); the round predicate and the recursive
bridge to `badAlpha` stay literal. In the D2 application the premise is
discharged from the accepted prefix. Per-round bound 27 is unchanged.

## Lead: B2 instance, part 2 — semantic messages and opening view (SemView.lean)

B2 interface fix (v8-r0-close lean/R0C/SemStatement.lean): `Msg.beforeZ0`
now carries the step-3 point claims `y : Fin 3 → Fin 29 → K`, which the
prover sends after α₁₀ (v6_onefold_prover.rs:568); `roundBad`'s z₀/z₁
clauses updated. Attempt 636 (SemStatement) and 639 (CircleRows, its only
dependent) exit 0, axioms unchanged. SHA-256 `85158bd62f64f189bd098424caee2b92abaf6808ab5cdd0d3b81f0f51eee0e57`.

`SemView.lean`: `SemMsg` (none / h1 commitment / round polynomial);
`succCarry`, `successorPoint` (state_only_poseidon.rs:95–105, polynomial
binary increment from coordinate 9), `xor12Point` (:109–117, coordinates
7 and 6); `toR0` (source MSB-first → R0 `eqWeight` LSB-first);
`openingPoints α`; `TypedContext` (public input, words, subfield typing);
`semChals`, `openingRounds` parsers; `openingStmt` (R0FS.Stmt with
`points := openingPoints α`, `pointClaims := y`,
`inactive := copyInactiveRows`, `semantic := True`); `openingView`
(24 semantic rounds, `(beforeZ0 y, circle z0)`, `(beforeZ1 _, circle z1)`,
opening rounds; none when malformed, z₀ = z₁, or a circle point is
base-rational). Attempts 637 SemSource (2.77 s), 638 (lint on a dropped
sanity example), 640 SemView exit 0, 3.01 s, 6807524 KiB, swap 0, 24+7 GiB.
SHA-256 `5fd27a6dd3d645fa02286c54faca51785f25e3295fc35a24fe71c60bfe63ac6d`. Axioms: standard three.

Remaining for the B2 instance: `semanticBad` (G13′), `decision` (the
sumcheck checks on the 24 rounds plus the opening decision through
`openingView`), then D3 and D2.

## Lead: B2 instance, part 3 — terminal at a point and decision (SemDecision.lean)

`scalarLaneAt`/`laneAt` (the 29 θ-lanes at explicit openings, h1 and
selector, in `laneOf`'s order) with `laneOf_eq_laneAt` by unfolding;
`eqValue` (T:1201–1213); `selAt α := eqWeight (toR0 α)` (the point's
selector vector), `activeAt`; `terminalValue` = `terminal_parts(...).0`
(T:1285–1310) at claims y and point α; `sumcheckChecks` (degrees ≤ 27,
boundary from claim 0, chaining, final value = terminal); `semPolys`
(round polynomials from rounds 14–23); `decision` (B2's decision: parsed
semantic checks ∧ `R0FS.decision` on `openingView`). Attempt 641 green
with lints, 642 exit 0, 3.03 s, 6804168 KiB, swap 0, 24+7 GiB. SHA-256
`2222c13112711d546abe18e524be3ae5c1d67b95f8be0ad59d2ad22226c47727`. Axioms: standard three.

B2 data now fixed: context, witness, messages, openingView, decision.
Open: `semanticBad` (G13′'s `semRoundBad` over `Lambda x.W`), then
D3 (`semantic_sound_closed` + the honest-claims bridge: for the extracted
candidate t, `pointClaims j = MLE of t at openingPoints j` from the
opening layer's `Witness`, so `terminalValue` at Boolean rows is the
batched row value, `hG`) and D2 (per-round densities).

## G14: SemBridge degree-route stop

Started from `9bc5f6b34`, with the lead's fixed `SemDecision.lean` and `SemView.lean`. The prescribed auxiliary claim in obligation 5, that **each** `honestClaims t v j l` has `MLDeg 1`, is false for the successor opening `j = 1`. Per the stop rule, no definitions or requested bridge statements were changed. Obligations 1–6 are not claimed complete, and no `virtual_indDeg` theorem is asserted. This finding refutes that auxiliary multilinearity assertion; it does not establish that the final `IndDeg 27` statement itself is false.

### Exact construct and symbolic witness

`SemView.lean:33–39` defines the literal polynomial carry and successor, matching `crates/aspis-statement/src/state_only_poseidon.rs:95–103` at Rust inspection pin `e4d68a70d3f6beb215c9f6dd418f4a2a3740c809`. `SemView.lean:45–51` reverses the coordinates and uses `toR0 (successorPoint v)` at opening index 1. `v8-wide-reference-20261005/lean/R0/OpeningDefinitions.lean:31–32` defines the Boolean product `eqWeight`; `R0/RoundNormalization.lean:28` defines the opening layer's `dot` as the weighted sum. `LaneMap.lean:78–83` identifies source coordinates 8 and 9 with the row's low bits 1 and 0.

Take a trace column whose Boolean row value is the product of those two low bits. Symbolically factoring the equality-weight sum gives the product of point coordinates 8 and 9: every other coordinate contributes `(1-u)+u = 1`, while each selected low bit contributes `u`. This is a source-level algebraic calculation, not a newly claimed Lean dot/trace bridge; no trace, row list, or universe was evaluated.

For `v 8 = y` and `v 9 = x`, the literal successor gives

```
q 8 = y + x - 2*y*x
q 9 = 1 - x
q 8 * q 9 = y + (1 - 3*y)*x + (2*y - 1)*x^2.
```

At `y = 0`, that honest successor-opening coordinate is `x*(1-x)`. It is not affine as a field-valued function when `2 ≠ 0`, in particular in characteristic `2^31 - 1`: values at 0 and 1 force both affine coefficients to zero, while the value at 2 is `-2 ≠ 0`. `SemBadSets.MLDeg` (`:299–303`) requires an affine polynomial on every such coordinate line when its bound is 1. Thus multilinearity in the opening point does not imply multilinearity after the source's polynomial successor substitution.

The smallest source-preserving statement repair is to separate opening indices: current and xor12 openings can retain the multilinearity claim, while the successor opening needs its actual composition-degree bound (the direct ten-factor estimate gives at most 10). The terminal's degree-27 proof must then account for the successor opening separately and verify the aggregate bound. No such repair or bound substitution has been made; that is a lead decision. No family residual exceeding degree 26 has been established by this finding.

### Checked finding and evidence

New `SemBridge.lean` imports the two requested modules and proves six audited symbolic lemmas: carry 0, carry 1, successor coordinates 8 and 9, their product under `v 8 = 0` and `v 9 = x`, and the absence of an affine representation of `x*(1-x)` under `2 ≠ 0`. These inspect only the first two carry steps and field arithmetic. They do not claim `eqWeight_bool`, `terminalValue_bool`, an honest-claims degree theorem, `virtual_indDeg`, or the acceptance bridge.

Coordinator attempt `run2.sh 2000 R0P/SemBridge 7000 7` passed on the pinned Lean 4.32.0 build host/cache: actual Lean exit 0, scope/time exit 0, wall 2.95 s, peak RSS 6,802,040 KiB, swaps 0. Reservation 24 + 7 GiB; MemoryHigh 5 GiB, MemoryMax 7 GiB, MemorySwapMax 0. All six audits use only `propext`, `Classical.choice`, `Quot.sound`; no warnings or errors. There was no failed attempt, unchanged rerun, cap increase, or dependency rebuild. The checked frozen source SHA-256 is `ea764ba59885f4c824d470032d53540ff005c5b4c238eb539f5721c93d560cdd`.

Cached dependency sources match the repository: `SemDecision.lean` SHA-256 `2222c13112711d546abe18e524be3ae5c1d67b95f8be0ad59d2ad22226c47727`; `SemView.lean` SHA-256 `5fd27a6dd3d645fa02286c54faca51785f25e3295fc35a24fe71c60bfe63ac6d`. Raw host evidence and snapshot are `evidence/out-2000.log`, `time-2000.log`, `sha-2000.txt`, `source-2000.lean`; verified local copies are under `/tmp/r0-sembridge-20261008/evidence/`. The coordinator independently reviewed the source calculation, worker proofs and final diff and ran the focused check. G14 is stopped at this exact degree-route assertion; existing model and family files remain unchanged.

### Continuation G14′ — independent-input weighted-degree stop

Resumed from lead commits `5db2ea394` and `853bc5568`, preserving the six accepted G14 finding lemmas. The new fixed criterion assigns weight 1 to current/xor12 openings and every selector input, weight 10 to successor openings, and requires every residual monomial to have weighted degree at most 26. The literal Poseidon leading branch has a nonzero weight-27 term under exactly this criterion. This is a completeness-audit finding against the prescribed criterion; it does **not** establish that the source's actual per-challenge-coordinate degree exceeds 26 or that `VirtualDeg` is false.

`Poseidon.lean:202–207` applies the leading external layer and two quintic full rounds. Its literal residual at `:344–352` contains `-block * low 0 * poseidonLeadingPair o.z o.xor12 lane`, with the two separate selector factors retained. Rust `state_only_poseidon.rs:389–398,589–615` has the same leading pair and selectors. Take `o.z` to be the constant vector x, xor12 and successor openings zero, `block = a`, `low 0 = b`, and all other low weights zero. The matrix in `Poseidon.lean:31–41` sends a constant vector x to 7x; the external layer at `:45–53` sends it to 35x. The leading coefficients through the three linear layers and two powers are therefore

```
x → 35*x → 35^6*x^5 → 35^31*x^25.
```

Round constants contribute only lower-degree terms and were not evaluated. The residual thus contains `-35^31 * a * b * x^25`, of prescribed weighted degree `1 + 1 + 25 = 27`. Its coefficient is nonzero in characteristic `2^31 - 1`. Equivalently, a selector vector supported only at row 0 makes both selector factors the same variable s, giving `-35^31 * s^2 * x^25`. Other local-row branches vanish in this specialization. Constant linear packing cannot erase its four equal nonzero base coefficients under `PackBasis.indep`.

The distinction from the actual coordinate bound matters: at `selAt v`, high and low selectors depend on disjoint groups of coordinates. In a fixed source coordinate, only one of the two outer selector factors varies. The uniform independent-input weight 1 assigned to both factors loses this fact. The smallest source-preserving correction is a coordinate-sensitive audit (or a proved high/low selector-support rule) rather than the current single scalar weight for every selector input. No such correction has been applied. The listed fixture `examples/v8_intrinsic_degree_audit.rs:1–14,35–58,138–188` checks an atomic-v3 affine-column family and explicitly calls itself a lower-bound witness together with a separate source upper bound; it is not a universal proof of this pair-forest independent-input criterion.

`SemBridge.lean` adds three checked support lemmas: `poseidonMat4_constant`, `poseidonExternalLinear_constant`, and `weighted_witness_degree` for `C (-35^31) * X^27`, with the coefficient kept symbolic under `35 ≠ 0`. Identification of the actual leading-pair coefficient above is a symbolic source audit, not a newly claimed Lean coefficient theorem for the constant tables. No `HonestRows`, `VirtualDeg`, or `ChecksAccept` completion is claimed. Work stops at the fixed criterion; no model, family, constant or lead file was edited.

Coordinator attempt `run2.sh 2001 R0P/SemBridge 7000 7` passed on the pinned Lean 4.32.0 build host/cache: actual Lean exit 0, scope/time exit 0, wall 3.27 s, peak RSS 6,810,576 KiB, swaps 0. Reservation 24 + 7 GiB; MemoryHigh 5 GiB, MemoryMax 7 GiB, MemorySwapMax 0. All nine declaration audits, including the six unchanged earlier lemmas, use only `propext`, `Classical.choice`, `Quot.sound`. No warnings, errors, failed attempts, cap changes, dependency rebuilds, or trace/row/universe/table/permutation evaluation. Frozen source SHA-256: `fe026af913107a06834976b53f2545644d8babad418872e758b4a332b10d2217`.

The cached `SemD3` source matches lead `853bc5568`, SHA-256 `4341beac41c7e7826ca88385a48bb8b10977ffa43a87cbc910243c4e6595c7fc`. Raw host evidence is `evidence/out-2001.log`, `time-2001.log`, `sha-2001.txt`, `source-2001.lean`, with verified local copies under `/tmp/r0-sembridge-20261008/evidence/`. The coordinator independently reviewed the scalar specialization, linear-layer arithmetic, source scopes, frozen diff and focused check. G14′ remains stopped at this exact criterion.

## Lead decision after G14 stop: weighted individual degree

G13′ (9bc5f6b34) and G12′ (`SemClosed` recompiled) accepted. G14's
finding (828cf122a) is accepted and the lead's item 5 was wrong as posed.

Facts: prover and verifier both use the composed successor claim
`MLE_t(successor_point(X))` (state_only_candidate_prefix.rs:255–262;
state_only_verify.rs:282–285), and `MLE_t ∘ successorPoint` is not
multilinear: in source coordinate c it has individual degree up to the
number of coordinates whose carry chain reaches c (10 for the LSB; for
n = 2 the term `(2X₁−1)(t₀₀−t₀₁−t₁₀+t₁₁)·X₀²` survives). `xor12Point` is a
coordinate-wise affine map, so `MLE_t ∘ xor12Point` is multilinear.

Why the bound 27 still holds: individual degree of a sum is the maximum
over terms, and the successor opening enters each family additively or in
low-degree products (Poseidon `next − f(cur)`: max(10, 25); path
`(1−bit)(succ−cur)`: 11; value range bits on `succ`: 20; schedule: 10).
The source's audit (`v8_intrinsic_degree_audit.rs`) measures exactly this
composed degree and asserts 26/27.

Corrected criterion for `IndDeg 27 10 G`: assign weights 1 to z-openings,
xor12-openings, selector weights and `eqValue`, and **10 to successor
openings**; every monomial of every lane's residual, as a polynomial in
these inputs, must have weighted degree ≤ 26. Then `MLDeg` closure
(`mlDeg_mul` adds, `mlDeg_add` takes max) with `MLDeg 10` for each
`honestClaims · 1` coordinate and `MLDeg 1` for the others gives
`MLDeg 27` for the virtual polynomial, hence `IndDeg 27 10 G`.

G14′ item 5 becomes: (a) `MLDeg 10` for `v ↦ dot (eqWeight (toR0 (successorPoint v))) (t l)`
and `MLDeg 1` for the z and xor12 claims and for `eqValue zc`;
(b) a per-family weighted-degree audit of the ported residual lists
(value, occupancy, asset, schedule, path, digest, poseidonPacked, copy,
and the μ terms), each monomial ≤ 26; (c) the closure argument. If any
family's residual exceeds weighted degree 26, stop and record it: that is
a completeness finding against the source's degree constant, not a
soundness finding, since `accept` enforces degree ≤ 27 on the prover.
Items 1–4 and 6 of G14 are unchanged.

## Lead: D3 core (SemD3.lean)

`honestClaims t v` (MLE of t at the three opening points of v, via R0's
`dot`/`eqWeight`), `preZc`, `virtualPoly pub B t pre` (the terminal at
the honest claims), the three G14′ bridge Props `HonestRows`,
`VirtualDeg`, `ChecksAccept` (over the challenge vector r), `fixedStrat`,
`candidateRoundBad` (G13′'s `semRoundBad` for one candidate with the
transcript's polynomials) and `semanticBadAt` (some candidate of
`Lambda x.W` is bad: B2's `semanticBad`); `d3_core`: a parsed transcript
passing `sumcheckChecks` with honest claims for a base-typed candidate t,
with no semantic round bad for t, gives `ProductionHolds ∧ CopyLinkBalance`
via `semantic_sound_rounds`. Attempts 643–646 were defeq/namespace fixes
(`0 + n`, `dot`, `List.length_ofFn`); 647 exit 0, ≈3 s, ≈6.8 GB (R0C
imports), swap 0, 24+7 GiB. SHA-256 `0b46c2e4d2622326276a28c07a73a484939a41a0a0a28ac415575a8f828e2dc2`. Axioms: standard three.

Remaining for B2's D3: the parse glue (`decision = true` ⇒ `openingView`
= some Q, `R0FS.decision Q om` ⇒ by `decision_true`/`accept_not_doomed`
with no opening round bad a `Witness` t, which is in `Lambda x.W` and
has honest claims; and `BaseTyped` from `Witness`'s subfield descent with
`Sfield l = F` for C1 lanes) — G15. D2 per round: `semRoundBad_card`
over `Lambda` (×100) under the duplex sampler law — G16, after the lead
fixes the sampler statement against R0C/V3/DuplexQ.

Correction: 4c785f9a6 was committed with a misplaced `omit` (attempt 647 exit 1, syntax); attempt 648 on the corrected file exit 0, no warnings. SHA-256 `26c5a9b3ba1d78052565929c92e6e257e63b58eab2695ea95936a41210c82c7f`.

Attempt 649: unused Algebra instance omitted; exit 0, no warnings.

## Lead: D2 rows for the semantic rounds (SemD2.lean)

Correction to the B2 instance: the semantic challenges are
`challenge_qm31` (aspis-core transcript.rs:378–392: four accepted limbs
< P), not the opening layer's 32-byte WideExact sampler. The SEM field is
therefore QM31 embedded in E = WideExact (K = E for the Lean objects,
challenges in the image of `algebraMap QM31Exact WideExact`), and the
ledger's denominator P⁴ is the right one.

`SemD2.lean`: `semanticBadRound x B polys i pref c` (some candidate of
`Lambda x.W` is round-i bad at fresh challenge c, earlier challenges
`pref` fixed); `semanticBadRound_card ≤ 100 · semRoundBudget i` (union
over `Lambda`, `Lambda_card`, `semRoundBad_card`; `Lambda` kept
irreducible). QM31 sampler model mirroring `R0C.ModuloField.ordinary`:
`qm31Rank : Fin (P⁴) ≃ QM31Exact` (`tupleFieldEquiv`), `qm31Sample`
(rejection-free reduction of one 32-byte block mod P⁴; the retained
retry implementation's law bridge is the same open item as the opening
layer's, close-job FS_LOG), per-element mass ≤ 1/P⁴ + 1/256³² =
(1+δ_q)/P⁴ with `deltaQ = P⁴/256³² ≤ 2⁻¹³¹` (`deltaQ_small`);
`semChal = algebraMap … ∘ qm31Sample` with `semChal_mass`
(injectivity) and `semChal_event` (`event_mass_le`);
`semantic_round_density`: mass of round i's bad set ≤
(1+δ_q)·100·semRoundBudget(i)/P⁴, with the α-round degree premise
`semRoundDegreeChecked` (authorized earlier). Attempts 650–652 were
instance binders, the `P` ambiguity (AspisCircleGroupOrder vs
AspisV5ComponentCQM31TowerExact) and qualified names; 653 exit 0, 3.69 s,
6836192 KiB, swap 0, 24+7 GiB. SHA-256 `b362eb6071084137f96cbf76258ad6915204f054ee1a89f160f16580de14b4ce`. Axioms: standard three.

With this, every per-row D2 bound for the 24 semantic rounds is proved
(sum 303000·(1+δ_q)/P⁴ ≤ 2⁻¹⁰⁵). Remaining: G16 assembles FS2.D2 for the
B2 instance from these rows under the duplex sampler program (one
squeeze per scalar round, as `R0C/V3/DuplexQ.round_field_bound` does
for the opening rounds), and the circle rows z₀, z₁ reuse
`R0C/CircleRows`.

## G15: SemD3Glue interface stop

Source review against lead `853bc5568`/`f1af33ad5` found two missing inputs in the proposed D3 route. No `SourceData` instance or `FS2.D3` proof is claimed, no extra theorem premise was installed, and no existing model or lead file was changed.

1. **Public-field typing is absent from the context.** `SemView.TypedContext` (`:53–58`) contains `pub`, `W`, and typing of the committed words only. `SemD3.d3_core` explicitly requires `PublicBase F x.pub`, while the generic B2 `SourceData` (`R0C/SemStatement.lean:45–51`) has no public-typing contract. The opening `Witness` (`R0FS/Protocol.lean:71–74`) provides candidate membership, point-claim equalities, and encoder subfield descent, not a fact about the separate public record. The authorized condition `Sfield l = F` for `l < 26` does not supply public typing.

   The new checked `exists_zero_context_not_publicBase` gives an explicit well-formed `TypedContext` with all words zero and `pub.assetId = B.i`. `PackBasis.indep` proves `B.i ∉ F`, so this context violates `PublicBase`. This is an interface counterexample, not a counterexample to the fully-premised `d3_core`. The smallest repair is to carry the source M31-public-field typing through the concrete context/parser, or a lead-authorized equivalent typed-context refinement; it cannot be inferred from word typing.

2. **The opening acceptance route lacks the sampler/guard facts.** `R0FS.decision_true` (`Hypotheses.lean:376–386`) exposes the five-round shape and `Accept`; it does not supply `γ ≠ 0` or `S.card = 22`. `R0FS.accept_not_doomed` (`:453–456`) requires both. The existing opening `d3` obtains them specifically from `SamplerLaws.nonzero` and `SamplerLaws.queryCard` (`:427–435`). The B2 `SourceData` and generic sampler arguments do not carry these laws.

   For the later requested q22 duplex sampler, the precise existing route is `R0C/V3/R0Q.lean:31–38,84–105`: `decisionQ` adds `cardOK`, and `d3Q` gets `S.card = 22` from that guard. A failed q22 scan returns the empty set (`V3/DuplexQ` module documentation), so the guard is material. The fixed `SemDecision.decision` (`:112–119`) instead calls plain `R0FS.decision` and has no `cardOK` conjunct. The checked `bad4_empty_false` confirms that the opening bad-query event, which itself requires 22 queries, does not reject an empty query set. `OpeningDefinitions.Accept` (`:109–115`) also has no query-cardinality clause. The smallest repair is to expose the actual nonzero-γ sampler fact and retain the q22 rejection/cardinality check at the combined decision boundary. No repair was made.

The requested restriction from full-prefix B2 `hitFrom` to opening-prefix `R0FS.good` was inspected structurally (`openingView` splits 24 semantic rounds, two circle rounds, then the opening suffix), but is not claimed proved or false: the proof stopped at the earlier missing inputs. Thus the complete requested chain to `InputNoteExtracted` remains open, as do G14′'s bridge hypotheses. This finding does not assert that an appropriately typed and guarded combined D3 statement is false.

New `SemD3Glue.lean` imports exactly `R0P.SemD3`, `R0C.SemStatement`, and `R0FS.Hypotheses`. It proves three bounded finding lemmas: `packBasis_i_not_mem`, `exists_zero_context_not_publicBase`, and `bad4_empty_false`. Coordinator attempt `run2.sh 2100 R0P/SemD3Glue 7000 7` passed: actual Lean exit 0, scope/time exit 0, wall 2.88 s, peak RSS 6,804,328 KiB, swaps 0. Reservation 26 + 7 GiB; MemoryHigh 5 GiB, MemoryMax 7 GiB, MemorySwapMax 0. All three audits use only `propext`, `Classical.choice`, `Quot.sound`; no warnings or errors. There were no failed attempts, unchanged reruns, cap increases, dependency rebuilds, or trace/row/universe/table evaluations.

Frozen source SHA-256: `4aeba7e579d17e36f496416355fe87b894430a7e4e8517e298c0897f89c1ad90`. Cached `SemD3` source matches SHA-256 `4341beac41c7e7826ca88385a48bb8b10977ffa43a87cbc910243c4e6595c7fc`. Raw host evidence is `evidence/out-2100.log`, `time-2100.log`, `sha-2100.txt`, `source-2100.lean`; verified local copies are under `/tmp/r0-semd3glue-20261008/evidence/`. The coordinator independently reviewed the interfaces, the exact q22 guard, the three proofs and frozen diff and ran the focused check. G15 is stopped pending those interface decisions.

### Continuation G15 — encoder-to-message descent stop

Resumed at lead `a3c82f3d3`. `TypedContext.pubBase` now supplies public typing, and `SemDecision.decision` includes `cardOK Q = true`. The earlier context counterexample is superseded and removed from the current module; its original source and evidence remain in commit `6e9d1bd6d` and attempt 2100. The two still-valid finding helpers are retained.

The explicit continuation stop condition applies: `R0FS.Witness` (`R0FS/Protocol.lean:71–74`) gives `exactInitialEncoder (t l) i ∈ Sfield l`, with `i : Fin 1048576`. `AspisR0.Opening.tuple_descent` (`R0/Binding.lean:105–115`), `binding` (`:129–133`), and `AspisWide.SubfieldDescent.initialCodeword_subfield_descent` (`Wide/SubfieldDescent.lean:58–69`) all conclude encoder membership. In contrast, `R0P.BaseTyped` (`CoreExt.lean:27–28`) requires `t l b ∈ F` for `b : Fin 1024`. `InitialMessage K` already is `Fin 1024 → K`, so this is a missing message-cell descent theorem, not an index conversion. The new checked `witness_c1_encoder_mem` proves exactly the encoder membership obtainable from `Witness` and `x.lanesF`.

No existing generic R0 lemma supplies the requested message membership. The closest result is `AspisWide.SubfieldDescent.initialMessage_fixed_of_agreement` (`:16–35`), which gives automorphism fixedness of the message from a sufficiently large agreement support. The smallest missing result is a message-level subfield-descent lemma with the existing support/agreement/received-subfield premises, concluding `∀ b, message b ∈ S`; the fixed-point lemma and Galois fixed-field criterion provide an apparent route, not a checked bridge here. The older `V7C1SubfieldRecovery.message_fixed_by_base_projection_of_large_shared_support` is specific to `QM31Exact` and assumes `InitialProjectionBinding`; it is not a generic replacement. Per the user's explicit stop rule, no new descent premise, model change, or bridge theorem was introduced.

The authorized opening sampler route remains `sampQ` at combined rounds 26–30, with `chalQ_lt`, `σQ`, and `gamma_ne_zero` as in `R0C.V3.DQ.d3Q`; it has not been instantiated in a combined `SourceData` proof after this earlier stop. No `FS2.D3`, full-prefix hit restriction, or `InputNoteExtracted` conclusion is claimed. G14′'s separately recorded bridge obligations remain open.

The coordinator recompiled the three requested dependencies sequentially, then checked the updated finding module. All jobs used pinned Lean 4.32.0, `run2.sh N R0P/<target> 7000 7`, reservation 24 + 7 GiB, MemoryHigh 5 GiB, MemoryMax 7 GiB, MemorySwapMax 0.

| Attempt | Target | Source SHA-256 | Lean / scope exit | Wall | Peak RSS KiB | Swaps |
|---:|---|---|---:|---:|---:|---:|
| 2101 | SemView | `d9eac6192f5627b8c58c0af0f492e36785de2f914264cca2156b781f8ef65e2a` | 0 / 0 | 3.05 s | 6,807,600 | 0 |
| 2102 | SemDecision | `cf8c98e1bf6d5da3a2e725efd3790c4efc7e75fc32b0c650c310d875bf1f8971` | 0 / 0 | 3.04 s | 6,807,036 | 0 |
| 2103 | SemD3 | `aa7b294e89dd8d2ba377f4b03e56efc22df7cb7793e80be6f222361dc774a68b` | 0 / 0 | 3.21 s | 6,810,380 | 0 |
| 2104 | SemD3Glue | `616cbd18178b2f3a773b03302127e0d50455309a2cd445a093718723c7d92e14` | 0 / 0 | 2.73 s | 6,804,512 | 0 |

All emitted audits use only `propext`, `Classical.choice`, `Quot.sound`; 2104 audits all three finding theorems. No warnings, errors, failed attempts, unchanged failing reruns, cap increases, package rebuilds, or forbidden evaluations occurred. Raw host artifacts are `evidence/out-N.log`, `time-N.log`, `sha-N.txt`, `source-N.lean`; verified copies are under `/tmp/r0-semd3glue-20261008/continuation-2104/`. The coordinator independently reviewed the descent interfaces and final source diff and ran the focused checks. G15 stops at encoder-to-message descent as instructed.

### Continuation G15 — message descent closed; semantic message-shape stop

Resumed after G17 at lead `ecb3118be`. The new `witness_baseTyped` applies `AspisWide.SubfieldDescent.initialMessage_subfield_descent` to each C1 lane using `witness_c1_encoder_mem` (the literal `R0FS.Witness.2.2` and `TypedContext.lanesF` projections). It proves `BaseTyped x.F t` with no new premise. The previous encoder-to-message stop is closed; `pubBase` and `cardOK` remain supplied by the lead's prior corrections.

The next source/interface mismatch is the semantic message shape needed by the `hitFrom` bridge. `SemView.semChals` (`:65–68`) reads the semantic challenge while ignoring the message. `openingView` (`:87–101`) uses that parser for the first 24 rounds, and `SemDecision.semPolys` (`:100–109`) inspects messages only at indices `14+j`. `SemDecision.decision` (`:117–126`) consequently does not validate the message tags of rounds 0–13. The source's schedule is documented in `SemView:4–12`, but no concrete source-indexed B2 `msg` definition or accepted-shape theorem enforces it. The generic `SourceData.protocol` takes an arbitrary `msg : Pf → Nat → Msg`; `Duplex.samp` also has no message-tag rejection check.

In contrast, `R0C.SemStatement.roundBad` (`:72–81`) can register a semantic event only when the current message is `.semantic sm`. Five new checked facts expose the precise mismatch without evaluating any trace or round range: `semChals_head_message`, `semPolys_head_message`, `openingView_first_message_eq`, and `decision_first_message_eq` prove that changing the first message leaves the parsers, opening view, and decision unchanged; `beforeZ1_semantic_not_roundBad` proves that a `.beforeZ1` message paired with a `.semantic` challenge misses all four `roundBad` branches, for every prefix and every `SourceData`.

Thus the proposed route from an accepted parse and no full-prefix hit to the `.semantic` tag required for each candidate's no-bad-round premise lacks a shape guarantee. This is a checked parser/classifier mismatch, not a claimed counterexample to the complete numerical or D3 statement. The smallest necessary lead correction is to connect an exact source-indexed message schedule to the protocol, or validate that schedule in the semantic-prefix parser/decision. No message-schedule hypothesis was added to D3, and no parser, event, sampler, or existing lead file was changed. The `sampQ`/nonzero-γ opening route remains authorized but is not claimed assembled after this stop. No `SourceData` instance, `FS2.D3`, or full-prefix/opening-hit restriction is claimed; G14′'s recorded bridge obligations also remain open.

All focused G15 jobs used pinned Lean 4.32.0, `run2.sh N R0P/SemD3Glue 7000 7`, reservation 24 + 7 GiB, MemoryHigh 5 GiB, MemoryMax 7 GiB, MemorySwapMax 0. G17's green object from 2300 was reused.

| Attempt | Source SHA-256 | Lean / scope exit | Wall | Peak RSS KiB | Swaps | Result |
|---:|---|---:|---:|---:|---:|---|
| 2105 | `6b19b2c49352b56198503c7309950678f27dcaa31e06724043264618b040bc68` | 0 / 0 | 2.81 s | 6,804,564 | 0 | Message-cell `BaseTyped` bridge green; four audits, no warnings. |
| 2106 | `d104f0906df1ab1f7c68c515f43870dc103180581cbecac827c890ef1dc5adca` | 1 / 1 | 3.16 s | 6,786,356 | 0 | Opening-view equality needed explicit suffix constructor cases; `decision` also needed namespace qualification. |
| 2107 | `7e2cef8b41939c1021455ab2382e8b7b8111de456db12805ca5eb16483116a8e` | 0 / 0 | 3.46 s | 6,825,028 | 0 | All nine theorems green; one unused `Fintype` instance warning. |
| 2108 | `984b1c03c943f5b32153bb65dcdea6a27655fd0a29730836d7202cc619e72ea1` | 1 / 1 | 3.18 s | 6,788,360 | 0 | The warning fix placed `omit` after the doc comment; moved it before the comment. |
| 2109 | `d42e808cff39273fa5f068f27d8efde024637721bfc5fa04b1d34dca68bd83ba` | 0 / 0 | 3.30 s | 6,825,116 | 0 | Frozen final source; nine permitted-axiom audits, no warnings or errors. |

The final audits use only `propext`, `Classical.choice`, `Quot.sound`. Raw artifacts are `evidence/out-N.log`, `time-N.log`, `sha-N.txt`, `source-N.lean`; verified copies are under `/tmp/r0-semd3glue-20261008/continuation-2109/`. Each failed attempt was followed by a source correction; no cap increase, unchanged failing rerun, package rebuild, or forbidden evaluation occurred. The coordinator reviewed the literal interfaces, theorem statements, final diff and hashes independently and ran every focused check. G15 stops at the newly recorded semantic message-shape gap.

### Continuation G15 — C2-aware instance and early degree-guard stop

Resumed at lead `84a2dce11`. Deleted all five previous tag-invariance finding lemmas as requested; the corrected `semChals` validates outer semantic tags and `openingView` reads and checks the round-2 C2 words. The earlier findings remain historical evidence only. The G17-based `witness_baseTyped` remains valid for a witness on the new C2-aware opening statement.

Added `sourceData B` with exactly the requested operations: 24 semantic rounds, `SemSource.semanticBad B`, `InputNoteExtracted`, `SemSource.openingView`, and `SemSource.decision B`. Added the value projection of a transcript carrying duplex states, its extension/round lemmas, and `duplexRows B budget`, which applies B2's doomed predicate to that projection. The budget is data for the separate row assembly; no probability or degree premise is installed.

The next literal gap occurs before the α phase. `SemD2.semanticBad` (`:116–120`) requires `degreeOK sm` at **every** round. `degreeOK (.roundPoly p)` requires `p.natDegree ≤ 27`. However, `semChals` accepts every inner `SemMsg` under the `.semantic` tag, `c2Of` inspects only index 2, and `semPolys`/`sumcheckChecks` inspect polynomial messages and degrees only at indices 14–23. Thus the proposed discharge of `degreeOK` from the α checks does not apply to an early `.roundPoly` payload, which the accepted-prefix parsers do not reject.

Seven new checked facts isolate this narrower issue. `semChals_semantic_head`, `c2Of_head`, `semPolys_semantic_head`, `openingView_semantic_head`, and `decision_semantic_head` retain the outer semantic tag and prove invariance under changing only its first inner payload. `semanticBad_roundPoly_high_false` proves that a payload of degree greater than 27 suppresses the event at every prefix; `semanticBad_X28_false` instantiates it with `X^28`, using only the symbolic degree theorem. These facts prove a parser/event mismatch; no complete accepted-transcript or D3 counterexample is asserted.

The smallest necessary correction is to justify the guard at early rounds: for example, apply the degree guard only in the α phase (where the stated count and acceptance checks need it), or enforce the actual inner-message schedule at the parser/decision boundary. This requires a lead decision. No existing definition or theorem premise was changed. Full D3, the opening-suffix `sampQ` integration, and the final no-hit-to-candidate bridge are not claimed. G18's padding lemmas and G16's semantic density work are independent of this stop; G14′'s separately recorded bridge obligations remain open.

Both coordinator checks used pinned Lean 4.32.0 and `run2.sh N R0P/SemD3Glue 7000 7`; MemoryHigh 5 GiB, MemoryMax 7 GiB, MemorySwapMax 0. Each runner recorded reservation 24 + 7 GiB; 2111 ran alongside the independent 2401 scope, below the host reservation limit.

| Attempt | Source SHA-256 | Lean / scope exit | Wall | Peak RSS KiB | Swaps |
|---:|---|---:|---:|---:|---:|
| 2110 | `af8f169cdd9405f43689583e76e1b0e15b5dca705d7892739f8d7a09703a5223` | 0 / 0 | 3.08 s | 6,814,900 | 0 |
| 2111 | `2ddf15efa9bfeabe759b89abc6dc05af247ce43e449b45640a1a8234ff5f3b54` | 0 / 0 | 3.71 s | 6,559,868 | 0 |

2111 is the frozen source: all 16 declaration audits use only the permitted axioms (some use fewer or none), with no warnings or errors. No failed G15 attempt, unchanged rerun, cap change, package rebuild, or forbidden evaluation occurred. Raw evidence is `evidence/out-N.log`, `time-N.log`, `sha-N.txt`, `source-N.lean`, with verified copies under `/tmp/r0-sem-continuation-20261008/g15-evidence/`. Lead dependency sources match the green 659/660/661/663 artifacts. The coordinator reviewed the new definitions, the restricted payload statements and the final source independently and ran the focused checks. G15 stops at the unconditional early-round degree guard.

### Continuation G15 — alpha-only guard; checked candidate bridge and pending D3 assembly

Resumed against lead `7d3aa4864` and the cached 664–670 objects. The obsolete unconditional early-degree findings were removed: the corrected classifier requires `degreeOK` only for rounds 14–23. Existing parser invariance lemmas about unused inner payloads remain valid. `SemPad` was recompiled unchanged as 2408 (Lean/time exit 0/0, 3.59 s, 6,830,940 KiB RSS, zero swaps, 24 permitted-axiom audits, no warnings; SHA `2734705552a97a2ef29f0a4c6c4a36fda6e2f7653fe972c7152f9896c91f13c1`).

Attempt 2120 checked the complete no-hit-to-candidate bridge, including C2-aware candidate membership, padding before C2, and current alpha-polynomial lookup. `no_hit_candidate_rounds` uses G18's `mem_Lambda_pad`, lambda/chi invariance and `polysOf_prefix`. `prefix_degreeOK` obtains the sole alpha guard from `sumcheckChecks`' degree conjunct. The full-prefix/opening restriction is proved by `opening_good_hitFrom`; the literal `sourceData` uses the prefix-based `semanticBad`. `witness_baseTyped` consumes `Witness.2.2` on encoder coordinates through G17's `initialMessage_subfield_descent` and `x.lanesF`. All 42 declaration audits in 2120 use only the standard three axioms, with no warnings or errors.

The pending final assembly derives the opening witness from `R0FS.decision_true`, `cardOK`, `R0FS.accept_not_doomed` and the opening-hit restriction; it derives nonzero gamma from the actual round-26 decoder `DQ.σQ` and `ModuloField.gamma_ne_zero`. It keeps the three named G14 obligations `HonestRows`, `VirtualDeg`, and `ChecksAccept` as hypotheses, exactly as `d3_core` does. This is not an unconditional completion of G14. The mixed sampler retains the full prefix's duplex state; row 30 is the literal q22 chain, with a pending symbolic equality to `DQ.sampQ` at local round 4, including its entire oracle-read trace.

| Attempt | Source SHA-256 | Lean / time exit | Wall | Peak RSS KiB | Swaps |
|---:|---|---:|---:|---:|---:|
| 2112 | `035cfbdb7e149045c7878c853eb507777b79234896d5f406f99f3cc1ae41d848` | 0 / 0 | 0:03.42 | 6838196 | 0 |
| 2113 | `6ca14b0f3aa8c4841df067ce027d9e31124e305cfc06b6ebe404b4f849ddeb5f` | 1 / 1 | 0:05.57 | 6780400 | 0 |
| 2114 | `e509964e28d161ae1f9ad0ec4d0c206d9df63268fc94fef70b4299ecbf18def9` | 1 / 1 | 0:04.52 | 6813832 | 0 |
| 2115 | `e692a0411b512912c503c6c8f66691f7f7d550e645c5a73034ecd67263e45ceb` | 1 / 1 | 0:05.88 | 6783032 | 0 |
| 2116 | `d52ae59f5e044c4011ed8d3e5d72230046eb68bbaa63fe8c3b15147085669aa8` | 1 / 1 | 0:05.81 | 6825996 | 0 |
| 2117 | `f17c552a07e1d3acd99357670d43610834c5dee1a08ad97371928f6cd0d7d007` | 1 / 1 | 0:05.64 | 6825692 | 0 |
| 2118 | `b83c30bcafd3554eed58e4ed782317d9126e8ba41d369e4425a45a110ff485f6` | 0 / 0 | 0:06.13 | 6874856 | 0 |
| 2119 | `6ba421783dbb8258b6fea5e0a15dc292a1ce6f0ec75ae5ab55d29078eae7aa15` | 1 / 1 | 0:06.09 | 6833320 | 0 |
| 2120 | `8cdd2b7fd002595d2736ddb620c81aee808d87447ff9a65fcb606e887782fc0d` | 0 / 0 | 0:06.44 | 6886784 | 0 |
| 2121 | `8ae2d638f986335bbde36f49681dee7ba23e01a552358707e83dc8e4f84bb6e4` | 1 / 1 | 0:07.89 | 6,848,240 | 0 |

2113–2114 corrected list-map/take and empty-parser option equalities. 2115–2117 corrected natural-number successor/C2 parser reductions and placement of `omit` before doc comments; 2118 was green. 2119 corrected dependent prefix lookups and C2-prefix length transport; 2120 was green. 2121 added the final assembly and failed on the `Table` namespace, the numerical opening offset, and cascading gamma/protocol elaboration; its failed audits are not proof evidence. Every failed rerun changed source; no cap was raised.

The corrected 2122 source is queued but **not compiled**, SHA `e0afd10de6252e6e1d2e7c31e9103581e5331cfc3ebeeb8460627570c6b4f545`. Host access failed before the next run: SSH to the Tailscale address timed out; direct Tailscale pings and `tailscale ssh` failed, and `tailscale debug ts2021` reported `x509: certificate signed by unknown authority`. The last checked whole-source milestone remains 2120, not the queued final D3 draft. No complete `FS2.D3` result is claimed yet.

All jobs used `run2.sh N R0P/SemD3Glue 7000 7`, MemoryHigh 5 GiB / MemoryMax 7 GiB / MemorySwapMax 0 and the host reservation check. Raw evidence is `evidence/out-N.log`, `time-N.log`, `sha-N.txt`, `source-N.lean`; local copies for 2112–2120 have matching snapshot hashes under `/tmp/r0-sem-rounds-continuation-20261008/g15-evidence/`. 2121's actual exit/timing were received from the runner before access failed; its raw files remain on the host pending copy. No local build, package rebuild, forbidden evaluation, new semantic premise, or security-setting bypass was used.

## G16: SemD2Glue pre-challenge degree-invariant stop

Reviewed the fixed semantic density theorem at lead `f1af33ad5`, B2 `SourceData`/state definitions, the duplex and q22 samplers, and the circle bounds. G15 currently supplies interface findings rather than the requested instance, so that dependency is also open. The independent blocking mismatch is the missing pre-challenge degree invariant for the generic D2 statement. No `FS2.D2` theorem, assembled 31-round protocol, new state predicate, or modified bad-round event is claimed.

### Decoder check and exact degree gap

There is **no** hard-coded WideExact challenge decoder in `FS2.Duplex.Params` (`FS2/Duplex.lean:61–71`). Its `dec : Bytes → Option M` parses messages; its challenge map is the independent generic `σ : Nat → State → Cv`. `Duplex.samp` (`:142–147`) returns that map's value and the next duplex state. A mixed challenge instance can therefore use `.semantic (R0P.SemSource.semChal s)` on semantic rounds without changing `Params`. The existing `R0C.V3.DQ` parameter and `sampQ` (`V3/DuplexQ.lean:45,60–67`) are the separate five-round opening instance; the combined protocol still needs its own mixed message/challenge instantiation and the usual value/state prefix projection. No decoder parameterisation change is required or made.

`FS2.D2` (`FS2/Statement.lean:177–182`) quantifies over **every** next message `m`, assuming only the prefix's round, the round bound, and that the prefix is doomed. B2 `doomed` is just absence of a payment witness and absence of a previous `hitFrom` (`R0C/SemStatement.lean:97–101`); it records no rejected-prefix or current-message degree status. The literal alpha round event in `SemRounds` bounds the honest polynomial but intentionally does not add a degree guard on the prover polynomial.

In contrast, `SemD2.semanticBadRound_card` (`:44–68`) and `semantic_round_density` (`:123–147`) require `semRoundDegreeChecked (fixedStrat polys) i pref`. Operationally checking the round polynomial before sampling is the correct source rule, but that check is not represented in this generic doomed-prefix premise. Full-transcript `sumcheckChecks`/`accept` can provide the degree bound only for accepted transcripts; D2 is not restricted to such transcripts. In particular, its arbitrary outgoing alpha message can contain `X^28`, regardless of earlier challenges.

The new checked theorem `degree_check_not_automatic` proves that the prescribed count premise is false for `fixedStrat (fun _ => X^28)` at round 14, for every earlier prefix. It establishes that degree validity is not automatic from the prefix's type; it is not a claimed counterexample to the full numerical D2 conclusion. The requested discharge point for `hchecked` therefore does not exist in the present route.

The smallest compatible repair is to model the already-performed rejection check at the state/protocol boundary: invalid-degree messages must leave the extension doomed, allowing the D2 proof to split into a rejected case and a degree-valid case. A source-faithful equivalent restriction may also work, but it requires a lead decision. Merely adding `hchecked` as a hypothesis to the fixed `FS2.D2` goal, or inserting a guard into the literal round predicate, would change the requested statement/interface and has not been done.

The complete prefix parse/hit bridge was not claimed in the absence of G15's instance and this invariant. `CircleRows.z0_density`/`z1_density_le` are explicitly ideal uniform-circle laws; applying them to the combined byte sampler also still needs that sampler's circle law. The existing five-round q22 instance and the semantic QM31 density theorem were reused for inspection, not silently substituted for a combined protocol.

### Checked finding and evidence

`SemD2Glue.lean` imports the four requested modules (the current G15 file records its stop) and contains the single audited degree-check finding. Both attempts used pinned Lean 4.32.0 and `run2.sh N R0P/SemD2Glue 7000 7`, with reservation 24 + 7 GiB, MemoryHigh 5 GiB, MemoryMax 7 GiB, MemorySwapMax 0.

| Attempt | Source SHA-256 | Lean / scope exit | Wall | Peak RSS KiB | Swaps | Result |
|---:|---|---:|---:|---:|---:|---|
| 2200 | `f1672167a3c4e300c28bb637f384c2da2963eef4c6fb6d8a029dfc14248552d7` | 1 / 1 | 2.55 s | 6,779,136 | 0 | A `dif_pos` proof lacked its expected type; source changed to give the explicit Nat inequality. |
| 2201 | `2570bc04d986db67bb05e7d4f73cafc5ff24d6b31642058cb73e2755a741c4a7` | 0 / 0 | 2.70 s | 6,814,436 | 0 | Final finding green; one permitted-axiom audit, no warnings or errors. |

The frozen source matches 2201. Its audit contains only `propext`, `Classical.choice`, `Quot.sound`. No unchanged failing rerun, cap change, dependency rebuild, or evaluation of traces, row ranges, field universes, or tables occurred. Cached `SemD2` source matches the lead file, SHA-256 `b362eb6071084137f96cbf76258ad6915204f054ee1a89f160f16580de14b4ce`; the host's green G15 object from 2100 was reused. Raw host evidence is `evidence/out-N.log`, `time-N.log`, `sha-N.txt`, `source-N.lean`; verified local copies are under `/tmp/r0-semd2glue-20261008/evidence/`. The coordinator independently reviewed the decoder, D2 quantifiers, state predicate, count premise, finding proof and final diff and ran the focused checks. G16 is stopped at the missing rejected-prefix/degree-validity bridge and the recorded G15 dependency.

### Continuation G16 — semantic row bounds proved; circle sampler interface open

Resumed at lead `84a2dce11` with the new `SemSource.semanticBad B`, including its internal current-message degree guard. Removed the superseded external-degree finding from `SemD2Glue.lean`; its earlier evidence remains above. The semantic decoder is exactly `semChal`, the lead's QM31 reduction embedded in `WideExact`. `Duplex.Params` is already parameterized by its challenge type and decoder, so no decoder parameterization change is needed.

Proved `hitFrom_append` and `doomed_ext_roundBad`: when a doomed prefix becomes not doomed on one extension, its new message/challenge pair has the current `roundBad`. `early_roundBad_semantic` isolates the semantic branch for indices below 24, and `early_nonsemantic_stay` excludes a flip for nonsemantic outgoing messages. `semantic_row_D2_semantic` then applies the exact `Duplex.samp_mean` one-block law, pointwise event containment, and `semantic_round_density`. `semantic_row_D2` covers every outgoing message, with zero flip mass for the other message constructors. The bound is `(1 + deltaQ) * (100 * semRoundBudget i / P^4)` for each semantic index, with the decoder identity `p.σ i a = .semantic (semChal a)` specifying the prescribed sampler. There is no external degree premise: `semanticBad`'s guard supplies the premise used by the lead's counting lemma. The independent early-degree coverage finding in G15 does not invalidate this density statement.

This is the 24 semantic-row component, not the full 31-round `FS2.D2` instance. The concrete remaining source interface is at circle rows 24/25: `R0C/CircleRows.lean:59–71` proves event densities for a **uniform `Point K`**, and its header explicitly excludes byte-state/source sampler laws. `R0C/CircleSource.lean:30–77` proves non-rationality/distinctness only for successful bounded source outcomes; error outcomes remain explicit. Neither interface defines the total mixed byte sampler needed here. A source-faithful mixed sampler with explicit abort treatment and the corresponding two circle event-density/refinement lemmas is the smallest missing bridge; no uniform-byte law or default challenge was assumed. `R0C/V3/DuplexQ.lean:35–59` supplies four field rounds and the q22 completion chain, not circle challenges. Reusing its opening law at offsets 26–30 and connecting the projected suffix remains assembly/proof work; it is not asserted to be a separate impossibility. Full D2 is stopped at the circle sampler interface, and no existing definition or premise was changed.

All coordinator runs targeted only `R0P/SemD2Glue`, pinned Lean 4.32.0, `run2.sh N R0P/SemD2Glue 7000 7`, MemoryHigh 5 GiB / MemoryMax 7 GiB / MemorySwapMax 0, with populated reservation 24 + 7 GiB.

| Attempt | Source SHA-256 | Lean / scope exit | Wall | Peak RSS KiB | Swaps |
|---:|---|---:|---:|---:|---:|
| 2202 | `8a3503dd93e4d71afb80f224841b49370af62fdd26e4e40746f53a4980ef0050` | 1 / 1 | 4.49 s | 6,798,380 | 0 |
| 2203 | `f66b4b095f8aef1dd68feca2e73a3618bc5d6ac25c015e5e2fa1a679a216735f` | 1 / 1 | 4.72 s | 6,797,040 | 0 |
| 2204 | `ac0a6d527059a44c082f2ab9cc4420a4995e9fd54b7db287a7d09a3eeb633986` | 1 / 1 | 5.54 s | 6,804,192 | 0 |
| 2205 | `a4dc21f0a5fe9a083febdd2d60efe56859ef33a07bc91a1eec0341872470244c` | 1 / 1 | 4.71 s | 6,802,636 | 0 |
| 2206 | `099cbfcb813cd89a0c412074e97d2d8d04c3c90fde3ba4b481236f62f8edde6e` | 0 / 0 | 5.31 s | 6,840,092 | 0 |

2202 corrected the state namespace, singleton-hit disjunction and round offsets; 2203 corrected the challenge type and made the sampler-law predicate explicit; 2204 isolated the three constant-zero mean branches; 2205 corrected a parenthesis in their nested mean expressions. Every failure was followed by a source change. Frozen 2206 has six theorem audits, all using only `propext`, `Classical.choice`, `Quot.sound`, and no warnings or errors. Raw artifacts are `evidence/out-N.log`, `time-N.log`, `sha-N.txt`, `source-N.lean`; SHA-verified copies are under `/tmp/r0-sem-continuation-20261008/g16-evidence/`. The coordinator independently reviewed the event containment, decoder identity, mean calculation, source interfaces and final diff, and ran all focused checks. No cap increase, unchanged failing rerun, package rebuild or forbidden evaluation occurred.

### Continuation G16 — opening-row integration and pending 31-row check

Resumed against lead `7d3aa4864` and cached 664–670. Attempt 2207 recompiles the existing six semantic-row declarations cleanly. The pending continuation relates the literal q22 sampler's `independentMean` to `DQ.Q22.chainE` by induction on the chain length, and contains the four field-opening row bridge and the q22 row bridge using `DQ.round_field_bound` and `DQ.round_q22_bound`. Their parser-shape premises are internal helper inputs; the final draft handles malformed prefixes/messages by proving the flip event empty.

The final scratch assembly uses exactly the authorized budgets: `(1+deltaQ) * (100*semRoundBudget i)/P^4` for semantic rounds 0–23; `2/P^2` for circle rounds 24–25; `epsilonSlack WideExact delta0 (i-26)` for opening rounds 26–30. Its only sampler hypotheses fix the source decoders (QM31 semantic reduction, `circleSample`, and `DQ.σQ`); no degree, density, accepted-prefix or witness premise is added. Row 30 uses the literal q22 chain directly. The alpha degree guard is already inside `semanticBad`, hence no extra degree premise remains in D2.

| Attempt | Source SHA-256 | Lean / time exit | Wall | Peak RSS KiB | Swaps |
|---:|---|---:|---:|---:|---:|
| 2207 | `099cbfcb813cd89a0c412074e97d2d8d04c3c90fde3ba4b481236f62f8edde6e` | 0 / 0 | 0:05.27 | 6837688 | 0 |
| 2208 | `cf6b7da1fb8c3779b41061b7b3f333a2caa810e3bd46fc8e0ea28c07aa15a312` | 1 / 1 | 0:06.75 | 6811920 | 0 |
| 2209 | `e17f0be8656e7a5dd223941f35f9cc8999b976ef7548f7c7a4838d78fd067a18` | 1 / 1 | 0:07.36 | 6817024 | 0 |

2208–2209 failed on namespace qualification, parser-structure projections, mean congruence and q22 output transport. The fixes are queued as unused attempt 2210, production SHA `cf446ca0547237dc38d09180482bd4bd6308019bd4b89e50aa6eb2c024416c01`. The 18 additional circle/malformed-prefix/final-assembly declarations are preserved separately at `/tmp/r0-semd2glue-20261008/D2Rows.lean`, SHA `da72a539eae4e684ba1ca210167c4f78320b624696c29d649073ef617b5bea86`; they remain uncompiled and require G19's mass theorems. Their final statement is `combinedProtocol_D2` on all 31 rows, but no full D2 result is claimed before checking it.

Jobs used `run2.sh N R0P/SemD2Glue 7000 7` with unchanged 5/7/0 GiB high/max/swap limits and reservation checks. Every failure was followed by source changes. Raw artifacts and hash-verified local copies are under the host `evidence/` and `/tmp/r0-sem-rounds-continuation-20261008/g16-evidence/`. Build-host Tailscale access failed before 2210; no local compilation or uncapped fallback was substituted.


## Lead decisions after G15 stop (context typing facts, q22 guard)

Both gaps (6e9d1bd6d) were lead interface omissions.

1. `TypedContext` now carries `F : Subfield K`, `lanesF : ∀ l < 26,
   Sfield l = F` and `pubBase : PublicBase F pub`: the statement's typing
   facts (C1 lanes and public fields are M31). `d3_core` takes
   `B : PackBasis x.F`, `hA : BaseTyped x.F t` and uses `x.pubBase`; G15
   obtains `BaseTyped` from `Witness`'s subfield descent via `lanesF`.
2. `SemDecision.decision` now requires `cardOK Q = true` (the q22 fibre
   count, the close job's `decisionQ` guard restated generically), so
   `accept_not_doomed`'s `S.card = 22` is available; `γ ≠ 0` is derived
   from the σQ sampler of the opening rounds exactly as `R0Q.d3Q` does
   (`chalQ_lt`, `σQ`, `gamma_ne_zero`), which fixes the B2 instance's
   opening-round samplers to `R0C.V3.DQ.sampQ`.

Attempts 654 SemView, 655 SemDecision, 656 SemD3, 657 SemD2: exit 0,
no warnings; axioms unchanged (standard three).

## Lead decision after G15 descent stop: message descent lemma (G17)

Accepted (356e07e66): `R0FS.Witness` types the encoder coordinates,
`BaseTyped` needs the message cells. No premise is added; the gap is a
true lemma of the encoder. `Wide/InitialEncoder.exactInitialEncoder`
evaluates the message's two polynomials at circle points whose
coordinates are `algebraMap (ZMod P) K` images, so it commutes with every
ring automorphism of K (`map_initialEncoder`), and
`Wide/SubfieldDescent.initialMessage_fixed_of_agreement` already shows
that an automorphism fixing the codeword on > 1024 coordinates fixes the
message. For finite K and a subfield S, the fixed field of the
automorphisms of K fixing S pointwise is S (finite extensions of finite
fields are Galois), so:

`initialMessage_subfield_descent (S : Subfield K) (m : InitialMessage K)
  (h : ∀ x, exactInitialEncoder m x ∈ S) : ∀ r, m r ∈ S`.

G17 proves it (new file in the sem-proof directory importing the Wide
modules), with support := `Finset.univ` (card 2²⁰ > 1024) and Mathlib's
Galois correspondence for finite fields; cite the exact Mathlib lemma
(fixed field of the full automorphism group over S equals S). G15's D3
then obtains `BaseTyped x.F t` from `Witness` and `x.lanesF`. If K is not
assumed finite in the Wide modules' statements, state the lemma with
`[Fintype K]` (the SEM field is QM31/WideExact).

## G17: Message-cell subfield descent

Completed `MessageDescent.lean` at lead `ecb3118be`, importing exactly `Wide.InitialEncoder`, `Wide.SubfieldDescent`, `Wide.EncoderLinearity`, and `Mathlib`. `AspisWide.SubfieldDescent.initialMessage_subfield_descent` proves the requested statement: subfield membership of every exact encoder coordinate implies membership of every message cell. Its instances are the existing Wide interfaces' `[Field K] [Fintype K] [DecidableEq K] [Algebra (ZMod AspisCircleGroupOrder.P) K]`; no additional descent or cryptographic premise is used.

For each `S`-algebra automorphism of `K`, `σ.commutes` fixes every codeword coordinate in `S`. `initialMessage_fixed_of_agreement` then fixes the message, using the full encoder support. The support-size proof rewrites `Finset.card_univ` and `Fintype.card_fin`, then proves the scalar numeral inequality `1024 < 1048576` with `norm_num`; it never evaluates the universe. Finally `IsGalois.mem_range_algebraMap_iff_fixed` gives membership in the range of `algebraMap S K`, and unpacking its subtype witness gives membership in `S`.

Exact Mathlib citations, at pinned revision `81a5d257c8e410db227a6665ed08f64fea08e997`: `Mathlib/FieldTheory/Galois/Basic.lean:343–345`, theorem `IsGalois.mem_range_algebraMap_iff_fixed` (through `mem_bot_iff_fixed` and `fixedField_top`); and the finite-target-field `IsGalois` instance at `Mathlib/FieldTheory/Finite/GaloisField.lean:197–206`. Applying that instance to the subfield type `S` and extension field `K` closes the transport with the canonical subfield algebra; `[Fintype K]` supplies finiteness, and the finite-dimensional instance is inferred. No `IntermediateField` conversion premise is needed.

Coordinator attempt `run2.sh 2300 R0P/MessageDescent 7000 7` passed first try: actual Lean exit 0, scope/time exit 0, wall 2.91 s, peak RSS 6,749,632 KiB, swaps 0. Reservation 24 + 7 GiB; MemoryHigh 5 GiB, MemoryMax 7 GiB, MemorySwapMax 0. The sole theorem's audit contains only `propext`, `Classical.choice`, `Quot.sound`; no warnings or errors. Frozen source SHA-256: `d3cb1623aeb04289250ed3f5bc2a9c532b62da2c5465933f2240fca47da856c3`.

Raw evidence: `evidence/out-2300.log`, `time-2300.log`, `sha-2300.txt`, `source-2300.lean`; verified copies under `/tmp/r0-messagedescent-20261008/evidence/`. The coordinator reviewed the proof and the exact pinned Mathlib lemmas independently and ran the focused check. No failed attempt, unchanged rerun, cap change, package rebuild, forbidden evaluation, or new finding. G17 closes the recorded encoder-to-message descent gap; G15 can consume it without adding a premise.

## Lead decisions after G15 message-shape stop: semantic tags and the C2 commitment

Accepted (3e46e7c00): `decision` did not validate the message tags of the
semantic rounds, so `roundBad`'s semantic branch was unreachable from an
accepted parse. Reviewing the fix exposed a second, more serious lead
omission: the source commits `(h1, G)` (lanes 26 and 27, the C2 fiber,
state_only_candidate_prefix.rs:506–524) *after* λ and χ, but `TypedContext.W`
fixed all 29 words in the initial context, `openingStmt` used `x.W`, and the
candidate list `Lambda x.W` was taken as if lanes 26/27 were committed with
the trace. A prover choosing H1 after χ was outside the modelled protocol.
`Lambda` is a joint width-29 list (`JointList.jointInitialList_card_le_100`),
so lanes cannot be separated per word; the λ/χ rounds therefore need a
candidate set determined before the C2 words.

Corrections (lead, attempts 659 SemView, 660 SemDecision, 661 SemD3, 663
SemD2; exit 0, no warnings, axioms the standard three; 662 was a first
SemD2 attempt with an `omega` context and two elaboration timeouts on an
untyped `⟨P.rounds.length, h⟩`, fixed by `h14'` and `Fin 24` ascriptions):

1. `SemMsg.h1 (h g : InitialWord K)` carries the two C2 words; `c2Of rounds`
   reads them from the message of round 2 (θ's round); `c2Words x h g` is
   `x.W` with lanes 26/27 replaced; `c2Base Sfield h g` (membership in
   `Sfield 26`/`Sfield 27`) with `c2Words_base`.
2. `semChals` requires `(.semantic _, .semantic c)` at every semantic
   round. `openingView` additionally requires `c2Of sem = some (h, g)` and
   `c2Base`, and builds the opening statement on `c2Words x h g`. Hence an
   accepted parse fixes the message tags of rounds 0–23 and the C2 words,
   and `R0FS.Witness` on the view's statement gives `t ∈ Lambda (c2Words x h g)`.
3. `SemD2.candidates x rounds sm : Finset (Trace K)` is the per-round
   candidate set: for `rounds.length < 2` the list of `c2Words x padWord
   padWord` (`padWord := exactInitialEncoder 0`) filtered to `t 26 = 0 ∧
   t 27 = 0`; at length 2 the list of the words with the *current* message's
   C2 words; afterwards the list of the words with `c2Of rounds`; `∅` when
   malformed. `candidates_card ≤ 100` in every case (filter of a `Lambda`).
4. `polysOf rounds sm : Fin 10 → K[X]` (round polynomials from the prefix's
   `roundPoly` messages at rounds 14 + j and from the current message);
   `degreeOK sm` (current `roundPoly` has natDegree ≤ 27);
   `degreeChecked_of_degreeOK` discharges G13′'s `semRoundDegreeChecked`
   for `fixedStrat (polysOf rounds sm)` at round `rounds.length`. This
   resolves G16's `degree_check_not_automatic`: a round polynomial of
   degree > 27 is rejected by `sumcheckChecks`, so it is not a bad event.
5. `semanticBad B P sm c` (B2's `SourceData.semanticBad`, prefix form):
   `∃ h : P.rounds.length < 24, ∃ cs, semChals P.rounds = some cs ∧ degreeOK sm
   ∧ ∃ t ∈ candidates P.statement P.rounds sm, semRoundBad t … (fixedStrat
   (polysOf P.rounds sm)) ⟨P.rounds.length, h⟩ (cs.getD · 0) c`.
   `semanticBad_card ≤ 100 · semRoundBudget ⟨P.rounds.length, h⟩` and
   `semantic_round_density` restated on it, for every prefix and message
   (no degree premise). `SemD3.semanticBadAt` (over `Lambda x.W`) is removed;
   `candidateRoundBad`/`d3_core` are unchanged.

Open for G18 (lemmas of the fixed objects, no new premises):
`lambdaRoundBad`/`chiRoundBad` read only columns < 26 (so they are invariant
under replacing columns 26/27 of `t` by 0), and padded membership:
`t ∈ Lambda (c2Words x h g) → Function.update (Function.update t 26 0) 27 0
∈ Lambda (c2Words x padWord padWord)` (the width-29 joint agreement set of
the padded tuple contains that of `t`: lanes 26/27 agree everywhere since
`padWord = exactInitialEncoder 0`). With `semRoundBad` at round 14 + j
depending on `strat` only through component j (`polysOf (prefix_i) sm_i j
= semPolys … j`), G15's D3 glue maps "no hit" to `¬ candidateRoundBad` for
the extracted t at every round. Lane 28 (D) remains in the initial context.

SemView SHA-256 `0186862718963200…`, SemD2 `fb7dba2dd9808721…`; 659
3.15 s / 6,816,140 KiB, 660 3.09 s / 6,806,912, 661 3.20 s / 6,810,340,
663 4.22 s / 6,841,244; swaps 0; 24 + 7 GiB, MemoryHigh 5 GiB, MemoryMax
7 GiB, MemorySwapMax 0.

## G18: Semantic padding and prefix-polynomial plumbing

Completed `SemPad.lean` against lead `84a2dce11`, importing only `R0P.SemD2`. `padC2Trace` is literally `Function.update (Function.update t 26 0) 27 0`. No new semantic, probability, typing or interpretation premise was introduced.

`lambdaRoundBad_pad` and `chiRoundBad_pad` prove the requested equivalences. The source inspection is stronger than the requested column bound: `Copy.lean:79–88` defines each endpoint tuple through a `Fin 16` column, hence every observed trace column is below 16, and in particular below 26. `LogUpAssembly.lean:27–64` obtains producer/consumer compressed values, `poleSet`, `valueSet`, `signedCount`, the polynomial multisets and `productDifference` from these tuples. The proof propagates the endpoint equality through these definitions symbolically; it never evaluates the pattern or link tables. `enabledLinks` depends only on `pub`. Neither event reads columns 26 or 27.

`mem_Lambda_pad` preserves every original `width29JointAgreementSet` position. Other lanes retain their original agreement; lanes 26/27 agree everywhere because `exactInitialLinear.map_zero` proves the zero message encodes to `padWord`. `Finset.card_le_card` then preserves the existing `mem_Lambda` threshold. `Lambda` is locally irreducible to keep elaboration and linting from unfolding its large representation; the proof uses its membership theorem. No agreement set, trace or row universe is evaluated.

`semRoundBad_strat_congr` rewrites only the strategy's current component at index `i−14` in the α phase, retaining the actual fixed prefix arguments. `polysOf_prefix` uses a parsed 24-round transcript and its current semantic message to identify `polysOf (rounds.take i) sm (i−14)` with `polys (i−14)` for `14 ≤ i < 24`. Substitution `i = 14+j` gives the requested slot statement. Its private `semPolys_getElem` helper extracts the parser fact symbolically for arbitrary `j : Fin 10`; no transcript-range enumeration is used. The statements require neither acceptance beyond the stated parse nor any probability claim.

The coordinator reviewed every final proof and independently checked the endpoint read boundary and event definitions. All runs used pinned Lean 4.32.0 and `run2.sh N R0P/SemPad 7000 7`, MemoryHigh 5 GiB / MemoryMax 7 GiB / MemorySwapMax 0. The runner recorded reservation 24 + 7 GiB; independent group scopes, where overlapping, remained below the host limit.

| Attempt | Source SHA-256 | Lean / scope exit | Wall | Peak RSS KiB | Swaps |
|---:|---|---:|---:|---:|---:|
| 2400 | `6357868c857067dbcf4e50b37dd408f364f8264224b3d0f254f38d4e94ffa941` | 1 / 1 | 3.20 s | 6,792,176 | 0 |
| 2401 | `b94e81e15a5f0dd5886353c5915d6ccfa7caaed9bbaa225a474db59b015cc8c1` | 1 / 1 | 3.42 s | 6,491,784 | 0 |
| 2402 | `7b131377e322f6fb232ef7a96fd27a7922eb345e17f4e9d8a1ddc44e9206c4f2` | 1 / 1 | 3.41 s | 6,792,116 | 0 |
| 2403 | `f87666b56597652983c9f7dabaf13262343aaeae145ae802ce8a4f9f8320ec1a` | 1 / 1 | 3.44 s | 6,793,544 | 0 |
| 2404 | `edb50e32ddb937a4c60f556a6f8c07c560fbc150e1b6b837ea92cb67e6dd1913` | 1 / 1 | 3.44 s | 6,793,684 | 0 |
| 2405 | `1cafa66bf6b7ad149d2a09bf08e713bfe3201c4abb6e3ccb30cb1397702e94e4` | 1 / 1 | 3.37 s | 6,794,128 | 0 |
| 2406 | `88ba6fe8fd0f7ce6f1510dcbdbe145735d18fbc1e49acef20f33bb95d73b2c43` | 0 / 0 | 3.57 s | 6,827,760 | 0 |
| 2407 | `2734705552a97a2ef29f0a4c6c4a36fda6e2f7653fe972c7152f9896c91f13c1` | 0 / 0 | 3.65 s | 6,831,112 | 0 |

2400–2402 corrected tuple/function congruence, update lemmas, placement of `omit`, and dependent list lookup rewrites; 2401/2402 also exposed unnecessary unfolding of `Lambda`, corrected by local irreducibility in 2403. 2403/2404 isolated a `signedCount` filter rewrite blocked by its hidden decision instance. The attempted Prop-predicate replacement in 2405 was ill-typed; 2406 instead proves equality of the producer/consumer value functions before rewriting inside the filter. 2406 was green with three unused-instance warnings; 2407 removes those unused binders (and the dependent χ theorem's binders). Every failing rerun changed source; no cap or recursion limit was raised.

Frozen 2407 has 24 declaration audits (23 theorems, including private helpers, and the padding definition), only `propext`, `Classical.choice`, `Quot.sound`, with no warnings or errors. Actual Lean and scope exits were inspected; the outer runner shell is not used as success evidence. Raw artifacts are `evidence/out-N.log`, `time-N.log`, `sha-N.txt`, `source-N.lean`; verified copies are under `/tmp/r0-sem-continuation-20261008/g18-evidence/`. No package/dependency rebuild, unchanged failing rerun, forbidden evaluation or source/interface obstruction occurred. G18 is complete; it does not claim to close the independent G15/G16 integration stops.

## Lead decisions after G15/G16 continuation stops (early degree guard, circle sampler)

1. Early degree guard (8f3799d30): accepted. `semanticBad`'s guard is now
   `14 ≤ P.rounds.length → degreeOK sm`: only the α phase has a verifier
   degree check (`sumcheckChecks`), so only there may a bad event be
   suppressed by it; earlier `.roundPoly` payloads (never parsed) carry no
   guard. `degreeChecked_of_degreeOK` takes the implication; the α-phase
   discharge in G15's glue is unchanged (`polysOf_prefix`, G18).
2. Circle rows (e335e8560): the source samples z₀, z₁ by
   `challenge_secure_circle_point` (transcript.rs:453–465): a `challenge_qm31`
   parameter t, mapped by circle.rs:55 (`secure_ood_circle_point_from_parameter`),
   rejecting t ∈ CM31 and retrying. The B2 instance models one block
   (`qm31Sample`, as the semantic rounds): with t.im ≠ 0 the point is
   `SamplerCirclePolicy.point t` embedded in WideExact (never BaseRational:
   `CircleSource.parameter_not_rational`); a rejected block is mapped to the
   base-rational sentinel `baseLift (1, 0)`, i.e. counted as `z0Bad`. This
   total one-block sampler is conservative for the source's retry loop
   (a rejection there is an error outcome); the retry-law bridge is the
   open item already recorded for the opening layer in the close job's
   FS_LOG. Masses: z₀ row ≤ (1+δ_q)·P²/P⁴; z₁ row ≤ (1+δ_q)(P² + 1)/P⁴
   (rejection, or the injective map hitting z₀); both ≤ 2/P².
   `R0C.SemStatement.rowBudget` rows `semanticRounds`, `+1` are now
   `2 / P^2` (lead skeleton edit; `CircleRows`' uniform-law lemmas are
   unaffected and recompiled).

Attempts 664 SemStatement, 665 CircleRows, 666 SemSource, 667 SemView,
668 SemDecision, 669 SemD3, 670 SemD2: exit 0, no warnings, standard
axioms; walls 2.8–4.1 s, peak RSS ≤ 6,839,896 KiB, swaps 0, 24 + 7 GiB.
Codex objects (SemPad, SemD3Glue, SemD2Glue) are stale against 664 and
must be recompiled in their next attempts.

G19 (Codex): `CircleSampler.lean` over WideExact: `circleSample : State →
Point WideExact` as above (embedding of `point t` by `algebraMap QM31Exact
WideExact`, `OnCircle` from `point_on_circle`), `circleSample_z0_mass ≤
2/P^2` and `circleSample_z1_mass (z0) ≤ 2/P^2` (via `qm31Sample_mass_slack`,
`event_mass_le`, `parameter_not_rational`, injectivity of the parameter
map — `t = y/(1+x)` — and a CM31 count `P^2`); then G16 completes the two
circle rows with decoder `.circle (circleSample a)`.

## G19: One-block circle sampler — checked definitions, mass proofs pending

Started from lead `7d3aa4864`. The sampler implements the authorized total one-block model: sample the source `qm31Sample` parameter; on `t.im ≠ 0`, embed `SamplerCirclePolicy.point t` into `WideExact`; otherwise return exactly `CircleRows.baseLift (1,0)`. This sentinel is the lead's counted rejection branch, not an additional challenge fallback. The source retry-loop refinement remains the separately recorded lead obligation.

Attempt 2506 checked the definitions `circleRejectPoint`, `embedCirclePoint`, `circleSampleParameter`, `circleSample`, and `embedCirclePoint_injective`: all five audits use only permitted axioms, no warnings/errors. The canonical `AspisV5ComponentCQM31TowerExact.QM31Exact` alias is required for the existing wide algebra instance. The similarly named older `ExactTowerBase.QM31Exact` exposed an instance mismatch; an attempted local algebra bridge was removed. No interface or new premise was introduced.

The remaining proof route is symbolic: the imaginary-zero parameter subtype is equivalent to CM31, whose cardinal is `P^2`; an accepted point cannot be base-rational; injectivity through `t = y/(1+x)` bounds each accepted point fiber by one; `event_mass_le`, `qm31Sample_mass_slack` and `deltaQ_small` give both requested `2/P^2` mass bounds. Neither mass theorem is currently checked. No mathematical/source obstruction has been established for this route.

| Attempt | Source SHA-256 | Lean / time exit | Wall | Peak RSS KiB | Swaps |
|---:|---|---:|---:|---:|---:|
| 2500 | `6569f6af18027cff6d5fbabd7d37d0ef5eecbd381359234bbb28a359fad5075b` | 1 / 1 | 0:00.95 | 2044296 | 0 |
| 2501 | `132a3dfe5cd2dca2a6c0e4226ac8e542d5b42f12b1afbd58551cfff29a2f70b3` | 134 / 0 | 0:13.83 | 7172932 | 0 |
| 2502 | `ea72feada8491895f869496cd8b4b7f45ea84acbaf70caf4d949b1bd8987be51` | 1 / 1 | 0:03.85 | 7128444 | 0 |
| 2503 | `2163f66dd212d321eeb46712f535e8158ad567c9edd139eadd0936506fc69f40` | 134 / 0 | 0:05.65 | 7172320 | 0 |
| 2504 | `fe4333b9a00cc715c5ea9a5f69229ecaba73566fcdac3d94cace2fb7c1869a45` | 134 / 0 | 0:05.12 | 7173052 | 0 |
| 2505 | `bf101e8f68e87fd42e5c555ba57b10e836dea6a9034de4c091b11b2982b0c547` | 1 / 1 | 0:04.48 | 7162272 | 0 |
| 2506 | `11c39b84e81191499d8bef0993eec7649250f7af88d8c603c0081161eb9e4c01` | 0 / 0 | 0:04.79 | 7200708 | 0 |
| 2507 | `65b73e09af93c606208f203008c800e21a4648fe3c81e47e2a46d26f1e5e808c` | 134 / 0 | 0:04.88 | 7170744 | 0 |
| 2508 | `b710c708b4d833ec338f380733110dee3916c67642884368ae44f5e8d27eeb8e` | 134 / 0 | 0:04.83 | 7170540 | 0 |
| 2509 | `ff60f57fcd07a110281b602289315d40ba6100f24117cd13e79d56993fd7f945` | 134 / 0 | 0:04.82 | 7171304 | 0 |

2500 exposed a missing optional cached import and was replaced by a local symbolic cardinality argument, without rebuilding dependencies. 2501–2503 exposed namespace/point/field-algebra mismatches; 2501 and 2503 then aborted for memory. 2504's local algebra-instance bridge also aborted and was removed. 2505 narrowed to sampler definitions and corrected the `baseLift` namespace; 2506 passed. 2507 restored the mass draft and aborted; 2508–2509 narrowed the cardinality work and removed local instance overrides but still aborted. The exact offending declaration is not yet isolated: empty captured output on an abort is not evidence that the first declaration failed, because output may be buffered. No unchanged failure was rerun and no memory/heartbeat/recursion cap was raised.

For the aborts, the runner's inner `exit=134` is authoritative: `/usr/bin/time` reported 0 for the wrapper despite the Lean abort. All swaps were zero. Each job used `run2.sh N R0P/CircleSampler 7000 7`, MemoryHigh 5 GiB / MemoryMax 7 GiB / MemorySwapMax 0 and the reservation check. Raw logs remain unmodified (2501 ends with a partial UTF-8 character); all local source snapshots match their `sha-N.txt` records under `/tmp/r0-sem-rounds-continuation-20261008/g19-evidence/`.

At the network stop, the proposed attempt 2510 source was frozen at SHA `bad7f533a55367837aca68ab4dc3e9bb5f6631c92c67605ea2a108b5ad3497ac`: it is the exact green 2506 source with only the fully qualified symbolic `cm31_card` lemma/audit appended, to isolate one declaration. The full canonical mass draft is separately preserved at `/tmp/CircleSampler-full-canonical-2507.lean`, SHA `4cccc38b9a9a13edfcb404aaa9022d97d90f5e642fb2516bb8cdf83aa759a89e`. Neither draft was compiled before the local continuation below. Tailscale peer pings and SSH timed out; its control-plane diagnostic failed certificate verification. No TLS verification bypass, local build, package replay, or source/interface change was attempted. G19 remains incomplete pending host access and focused proof checks.

### Continuation G19 — authorized local predecessor checks

The owner then instructed: “do what you can locally.” The coordinator reused the native macOS Lean 4.32.0 executable (commit `8c9756b28d64dab099da31a4c09229a9e6a2ef35`) and pinned Mathlib cache at `81a5d257c8e410db227a6665ed08f64fea08e997`. No package or dependency rebuild was started. Current `R0P`, `R0C` and `FS2` dependency objects are absent locally, so the full G15, G16 and G19 targets cannot be checked from that cache.

Four isolated mathematical predecessors now pass. `LocalCircleCount` checks `cm31_card`, the imaginary-zero subtype equivalence, and its `P^2` cardinality. `LocalCircleAlgebra` checks uniqueness/composition of maps out of `ZMod` (`RingHom.ext_zmod`), injective pullback of base-field equalities, and the generic rational inequality used to close the mass bound. This avoids requiring an extra scalar-tower instance. `LocalCircleGeometry` checks the actual canonical QM31-to-WideExact embedding, accepted-point non-rationality, and injectivity of the accepted parameter map. Non-rationality uses the same coordinate argument as `CircleSource.parameter_not_rational`, via `SamplerCirclePolicy.outside_point`; injectivity uses `point_injective`, hence the proved recovery formula `t = y/(1+x)`. `LocalCircleFiber` checks predicate-iff cardinality transport and the rejected-region plus one-fiber bound for arbitrary finite input types. No concrete universe is evaluated, and no new premise is added to either requested public mass theorem.

The exact cached geometry source hashes were reviewed against the prior source-pin and successful-build records: `R0/Chord` and `R0/ChordGeometry` match `/tmp/aspis-r0-resume/final/evidence/Final-*.json`; `WideTower` matches the committed `PORT_SCOPE`/`PORT_LOG` pins; `SamplerCirclePolicy` matches `r78-sampler-circle/SOURCE_PINS.json` and the R729 direct-import manifest. These are read-only caches; no earlier completed group was rebuilt.

| Attempt | Focused target | SHA-256 | Exit | Wall s | Peak aggregate RSS KiB | Child swaps |
|---:|---|---|---:|---:|---:|---:|
| 2510 | `LocalCircleCount` | `e65a1255ebb6d2c1a28f6b6ae0f060d600e10224df9e109484ef12b657d9c776` | 1 | 75.58 | 4051504 | 0 |
| 2511 | `LocalCircleCount` | `b781657979f4489afa31abc9d64bc22e8d7f1e606e329c748ccc49ddf4388766` | 0 | 69.05 | 4380720 | 0 |
| 2512 | `LocalCircleAlgebra` | `58da0c1328cff37ae35a2aa6fdb8217b405ee28df1afb65aa01e084d675fae9f` | 1 | 12.71 | 3375184 | 0 |
| 2513 | `LocalCircleAlgebra` | `2f729707ea4807c37aec170b13752488441471702da51bb933fa9a94930d2142` | 1 | 20.40 | 3333616 | 0 |
| 2514 | `LocalCircleAlgebra` | `72bba93bc10830853f75f35acc74fd83c38286a8f4a899b30fa507a2fd2104a4` | 0 | 21.05 | 3353760 | 0 |
| 2515 | `LocalCircleGeometry` | `10f6d81997eab2388f5624ab26950f2868c58a2e29eb2d6d0fdb1772fcc49752` | 0 | 66.43 | 4305552 | 0 |
| 2516 | `LocalCircleFiber` | `64e64c34865223938fdc77e584b1af3e808f859c1a8c1eb0b0d8020ebe25cf97` | 0 | 10.28 | 1899440 | 0 |
| 2517 | `LocalCircleHelpers` | `5a801348b06a097e6c8adcb112f494f7645fdf5cf071ca83d16c6791a851c0c6` | 0 | 76.91 | 4123088 | 0 |

2510 isolated a maximum-recursion-depth failure at `congrArg₂ Nat.mul` in the CM31 cardinal proof. 2511 replaces that elaboration with a named `ZMod.card` equality and a controlled rewrite; the three declarations pass with the default recursion limit. 2512 exposed two elementary division/association elaboration errors in the rational inequality. 2513 fixed the association but used an unavailable rewrite name; 2514 uses `div_eq_mul_inv` and passes. The inequality explicitly multiplies the bounds by nonnegative factors, rather than relying on nonlinear automation to discover these products. 2515 and 2516 passed first try. All four successful targets have only `propext`, `Classical.choice`, and `Quot.sound` in their 15 declaration audits, with no Lean warnings or errors.

Checks were serialized by the coordinator with `lake env lean -M7000 -j1`; a local watchdog stops the process group at 7 GiB aggregate RSS or 900 seconds. The runner later gained an explicit lock before the geometry check. No Lean memory, heartbeat, or recursion cap was raised. macOS has no Linux cgroup or per-job `MemorySwapMax=0`, so these are explicitly local development checks, not Linux scope evidence. Child resource records report zero swaps; system-wide swap usage was also recorded before/after and is not presented as a per-job guarantee. The largest measured aggregate RSS was 4,380,720 KiB. The empty scratch Lake manifest has no package dependencies; `lake env` was used only to launch the focused file checks.

Raw local evidence is `/tmp/r0-sem-local-20261008/evidence/{out-N.log,time-N.json,sha-N.txt,source-N.lean}`; all source snapshots were checked against their hashes. The coordinator reviewed and assembled the checked pieces into the literal `CircleSampler.lean`, SHA `bb3aa6e094298fd890f07c406bc00eda2725fd5e129a518f74171f0fb61d326d`. The five sampler/map definitions from 2506 remain byte-for-byte unchanged; the explicit sampler-policy import and pinned Rust source citations were added. The complete file, branch/cardinality composition, and final two mass-theorem instantiations remain unverified until the current R0P closure is available. This continuation does not claim full G19, D2, or D3 completion. The next unused G19 attempt is 2518.

A final focused compatibility check, 2517, copied 11 actual declarations verbatim from the assembled file into the cached tower/chord/policy environment. This was needed because the isolated cardinality test had imported only the canonical tower, while the real sampler also imports the older exact-tower namespaces. The combined check passed all 11 audits with the standard three axioms and no warnings, at 76.91 s and 4,123,088 KiB aggregate RSS. Together with 2506's unchanged literal definitions, this covers the mathematical helpers and sampler construction. The seven remaining declarations (branch rationality equivalence, bad-set definition/cardinality composition, specialized numerical bound, and two final mass theorems) are still unverified in the complete module. There was no package/dependency rebuild or unchanged failing rerun. A final five-second SSH access check still timed out. Sources and evidence remain uncommitted; no push or formal completion is claimed.

## Lead: G19 closed locally (CircleSampler.lean); the concrete-instance hazard

The build host was unreachable (Tailscale relay up, ssh/ping timing out),
so the lead built the FS/FS2/R0FS/R0C/R0P object chain locally
(`/tmp/r0-sem-local-20261008/build_chain.py`: one `lake env lean -M7000 -j1`
at a time, 7 GiB aggregate-RSS watchdog, 900 s cap, pinned Lean 4.32.0 and
Mathlib `81a5d257`; 87 modules, every one exit 0, peak 5,295,712 KiB,
swaps 0) except the Aeneas-dependent ones: no Lean 4.32 Aeneas objects
exist locally, so `R0C.CircleSource`, `R0C.V3.DuplexQ` and their dependents
(`SemD2Glue`) cannot be checked here. These are macOS development checks,
not Linux-scope evidence; the host runs are still required before commit.

Codex's assembled `CircleSampler.lean` (G19, uncommitted, host-unverified
beyond its 2506 definitions) failed locally at five places. Three were
mechanical (an `.elim`, `open FS` for `indicator_iff`, the unused
`R0C.CircleSource` import, which also pulls Aeneas). Two were
maximum-recursion failures with a single root cause, found by probes:
for a concrete predicate on `QM31Exact`/`Point WideExact` such as
`t.im = 0 ∨ (t.im ≠ 0 ∧ circleSampleParameter t = z0)`, instance search
builds a concrete `Decidable` term (`instDecidableOr`, M31/wide
`DecidableEq`) rather than the classical one; whenever the unifier must
compare such a term with the classical instance of another statement
(a `Fintype.card_subtype` rewrite, a generic helper whose own filter
instance is `instDecidableOr (propDecidable _) (propDecidable _)`, or a
`∈ Finset.univ` membership goal), it unfolds the decision procedure on
2³¹-sized `Fin` arithmetic (diagnostics: `Nat.rec`, `Fin.mul`, `point`,
`px`, `qm31R`). Rule adopted for every concrete-field file: predicates
are wrapped as `def`s (`rejectedPred`, `fiberPred`, so only
`Classical.propDecidable` applies), generic set lemmas take every filter
predicate as an atomic variable (`card_filter_le_add_of_cover`,
`card_filter_le_one_of_inj`), cardinalities go through explicit
equivalences (`Finset.card_eq_of_equiv_fintype`, `imZeroEquiv`,
`cm31_card`), and `circleSampleParameter` is `irreducible`. Codex's
definitions (`circleRejectPoint`, `embedCirclePoint`,
`circleSampleParameter`, `circleSample`), `cm31_card`, `imZeroEquiv`, the
`ZMod` pullback lemmas, `embedCirclePoint_not_rational`,
`circleSampleParameter_rational_iff`, `circleBadZ0_card`,
`circle_mass_bound_generic` and the two mass theorems' statements are
unchanged; `circleBadZ1_card` is restructured as above.

Local result: `R0P.CircleSampler` exit 0, 37.9 s, 5,114,800 KiB, 24 audits
with exactly the standard three axioms and two (`zmod_algebraMap_comp`,
`zmod_algebraMap_pullback`) with fewer; no warnings. Source SHA-256
`cab19ed14584dbc360bac56e419cd4df61d3c558fab4edfef46ed532d0f9b3f1`.
Host result (attempt 671, `sh run2.sh 671 R0P/CircleSampler 7000 7`,
source SHA identical): `exit=0`, wall 0:11.09, peak RSS 6,844,848 KiB,
swaps 0, no `error`/`warning` lines, the same 26 `#print axioms` lines as
locally. The host peak (6.5 GiB under `MemoryMax=7G`) is well above the
local 5.1 GiB; any later edit to this module should be re-measured with a
focused predecessor before the cap is relied upon, and the cap is not to be
raised.

Also found locally: Codex's uncommitted `SemD3Glue.lean` fails against
the current chain at `:901` (`AspisR0.RoundNormalization.dot` vs
`AspisR0.LinearDual.dot` in `honestClaims`; the glue must use
`LinearDual.dot` as `SemD3` does) and `:1017`/`:1012` (an unsynthesised
placeholder `w` and its unsolved goal in the protocol instance).

### G15 continuation — checked glue; fixed D3 obligation stops at G14

Source revision `04ada5752974bfe45bf665f6ddb21df6df653831`, plus the existing
uncommitted G15/G16 drafts. The honest-claims transport now explicitly changes
the witness equality to `AspisR0.LinearDual.dot` before applying `hα`; it does
not rely on namespace resolution. The explicit state witness `a` in
`combined_chal26` was already present in the resumed draft and is verified by
2123. Its value is the squeeze response after absorbing the global round-26
message, so `hσ26 a` supplies the literal `DQ.σQ 0 a` gamma output.

The checked file includes `candidate_mem_before_c2`, `candidate_mem_after_c2`,
`candidate_bad_to_prefix`, `no_hit_candidate_rounds`, and the q22 trace/output
bridge `combined_round30_sampQ`. The candidate proof uses the prefix's actual
`candidates`, G18's padding/strategy congruence, and `polysOf_prefix`. The only
filter-membership proof in this file is polymorphic in `K`; no new concrete
QM31/point filter predicate or concrete decision-instance comparison was
introduced. The existing G19 rule remains in force.

Both focused attempts ran on `dombarker@100.108.41.90`, in the existing pinned
workspace `/home/dombarker/project-offloads/aspis-fs-generic-20261006`, using
Lean 4.32.0 and the unchanged compiled dependency cache. `run_g15_lake.sh` is
the existing `run2.sh` scope/reservation wrapper with a separate runner that
invokes `lake env lean -j1 -M7000 -DElab.async=false`. Its minimal Lake project
has no dependencies; no package or dependency build ran. Reservations were
24 + 7 GiB, MemoryHigh 5 GiB, MemoryMax 7 GiB, MemorySwapMax 0, timeout 900 s.

| Attempt | Exact target | Lean / scope-time exit | Wall | Peak RSS KiB | Swaps | Axiom lines |
|---:|---|---:|---:|---:|---:|---:|
| 2123 | `R0P/SemD3Glue.lean` | 0 / 0 | 0:21.82 | 6,934,508 | 0 | 55 |
| 2124 | `R0P/D3ObligationStop.lean` (diagnostic) | 1 / 1 | 0:02.82 | 6,783,964 | 0 | 0 |

2123 source SHA-256:
`bf90c82dd174e4bbbf9c9145da8850ee05685378255e762c49510478da4d9a41`.
All 55 declaration audits use subsets of `propext`, `Classical.choice`, and
`Quot.sound`; no `sorryAx`, errors, or warnings. In particular:

```text
'R0P.SemD3Glue.accepted_no_hit_extracted' depends on axioms: [propext, Classical.choice, Quot.sound]
'R0P.SemD3Glue.combined_chal26' depends on axioms: [propext, Classical.choice, Quot.sound]
'R0P.SemD3Glue.d3' depends on axioms: [propext, Classical.choice, Quot.sound]
'R0P.SemD3Glue.combined_round30_sampQ' depends on axioms: [propext, Classical.choice, Quot.sound]
```

2124 source SHA-256:
`c0cb64816f4ae5d4f8d8d77ea85151a1e51cbbf6055c88a588b5e7f2e560a2f6`.
This isolated diagnostic imports the green glue and applies `d3` without
assuming the three G14 bridge Props. Lean stops at exactly:

```text
case hrows
⊢ ∀ (x : TypedContext SemE Sfield) (t : Trace SemE), HonestRows x.pub B t

case hdeg
⊢ ∀ (x : TypedContext SemE Sfield) (t : Trace SemE), VirtualDeg x.pub B t

case hchk
⊢ ∀ (x : TypedContext SemE Sfield) (t : Trace SemE), ChecksAccept x.pub B t
```

The complete context is retained in `out-2124.log`: it contains the fixed
characteristic, `B`, the mixed sampler parameters, messages, decoder, budget,
and `hσ26`, but none of these three semantic assumptions. The fixed
`SemStatement.Obligations` D3 conjunct does not supply them either. `SemD3`
defines them as Props and takes them as hypotheses of `d3_core`; `SemBridge`
contains the documented G14/G14′ findings, not proofs of those Props. Thus
2123 is a checked conditional assembly, not closure of the requested D3
obligation. This is a missing proof, not a claim that `VirtualDeg` is false.
No new premise, changed obligation, or claimed G15 closure was introduced.

Stopped per the owner's instruction. G16 was not started or edited; no final
manifest replay and no commit were made. No unchanged regression was rerun.
Verified snapshots, SHA records, complete axiom/goal logs, time logs and the
focused runner are retained in
`evidence/g15-stop-2123-2124/`; host originals remain in `evidence/`.

## Overnight G14′ — Step 0: verified conditional G15 checkpoint

The owner authorized committing the exact 2123-green `SemD3Glue.lean`
(SHA `bf90c82dd174e4bbbf9c9145da8850ee05685378255e762c49510478da4d9a41`).
Its conditional `d3` is an honest checkpoint: the three G14 hypotheses are
explicit Props, not premises added to `SemStatement.Obligations`. The 2123
host result and audits above remain the evidence; no unchanged rerun. Only
the Lean source and LOG are included in this checkpoint; evidence is excluded.

### Overnight Step 1 — SemAccept complete

Proved `Sumcheck.accept_of_checks` for arbitrary nonempty dimension by induction, then `SemSource.checksAccept` for every public input, packed basis and trace, with no semantic hypothesis. 2002 removed redundant dependent generalization; 2003 checked the generic lemma. 2004–2005 exposed the final list/slice and definitional-index transport, repaired by named slice equalities and `convert`/`rfl` on indices (not rows). 2006 is the complete frozen module: exit 0, no errors or warnings; `accept_of_checks` uses `[propext, Quot.sound]`, `checksAccept` uses `[propext, Classical.choice, Quot.sound]`. No unchanged rerun.

Host `dombarker@100.108.41.90`; pinned Lean 4.32.0 and existing cache, one Lean job at a time. The existing `run_g15_lake.sh` adapter retains run2’s reservation and scope limits and invokes `lake env lean`: MemoryHigh=5G, MemoryMax=7G, MemorySwapMax=0, 900 s timeout, reservation 24+7 GiB. No cap increase or dependency build. Raw host artifacts remain in `evidence/`; hash-verified local copies are at `/tmp/r0-g14-overnight-20261009/evidence/`. Evidence files are excluded from commits.

| Attempt | Target | exit / time exit | Wall | Peak RSS KiB | Swaps | Axiom lines | Source SHA-256 |
|---:|---|---:|---:|---:|---:|---:|---|
| 2002 | `R0P/SemAccept` | 1 / 1 | 0:02.78 | 6770824 | 0 | 1 | `d82d408e6842f55ab1b2b97c05629e1d0ecc7c376784ce727716cab33b078f8f` |
| 2003 | `R0P/SemAccept` | 0 / 0 | 0:02.79 | 6803960 | 0 | 1 | `03d0174b33a0214644178acb345c38cb8337acd6e76ebf91df27464855748d4b` |
| 2004 | `R0P/SemAccept` | 1 / 1 | 0:03.10 | 6772848 | 0 | 2 | `c7fce4daa83ad4455f9cceeac5151d31c8f1cfc0bb669eab6812ca27650a6941` |
| 2005 | `R0P/SemAccept` | 1 / 1 | 0:02.65 | 6772588 | 0 | 2 | `1b147e4060d78bfb78ce78302c3aeb4d2c13704d9d07489221d1c20f03f580c4` |
| 2006 | `R0P/SemAccept` | 0 / 0 | 0:02.81 | 6811528 | 0 | 2 | `02a046a9703bf95c8f5fa3cb489084e0862379ae6f020a48f0a4374b542019b4` |

Source revision(s): `eb8df067e84ff6bdec264b53f7440073f5dac54a`, plus the recorded source snapshots. Failed-attempt audit output is not accepted proof evidence.

### Overnight Step 2 — SemHonest complete

Proved the requested selector, dot, successor, XOR-12, honest-claims, equality-weight, active-selector and `honestRows` bridges. Every requested predecessor was host-checked before adding the next. The successor route uses a general binary-digit/carry-product induction and modulo-bit identity; it closed on its second attempt (2011). No rows, blocks, constant tables or permutations were enumerated. G2 layout inspection confirms `g2Row h l = 16*h.val+l.val`, with high coordinates 0–5 and low coordinates 6–9. 2007–2008 repaired the public row-bijection access and index reductions; 2010–2011 repaired the binary-helper elaboration; 2012/2014–2016 repaired Bool namespace and decision-instance transport in XOR; 2017–2018 repaired a forbidden reverse-def simp syntax; 2019–2020 removed an unused tactic and checked activeAt. 2021 is the complete module: 14 audits using subsets of the standard three axioms, no error or warning. Process deviation: 2013 accidentally repeated the 2012 source because a failed exploratory file lookup skipped the chained edit. The 3.09-second failed run is retained, not counted as progress; the local runner now rejects any previously attempted target/source hash before launching. No other unchanged rerun or cap increase occurred.

Host `dombarker@100.108.41.90`; pinned Lean 4.32.0 and existing cache, one Lean job at a time. The existing `run_g15_lake.sh` adapter retains run2’s reservation and scope limits and invokes `lake env lean`: MemoryHigh=5G, MemoryMax=7G, MemorySwapMax=0, 900 s timeout, reservation 24+7 GiB. No cap increase or dependency build. Raw host artifacts remain in `evidence/`; hash-verified local copies are at `/tmp/r0-g14-overnight-20261009/evidence/`. Evidence files are excluded from commits.

| Attempt | Target | exit / time exit | Wall | Peak RSS KiB | Swaps | Axiom lines | Source SHA-256 |
|---:|---|---:|---:|---:|---:|---:|---|
| 2007 | `R0P/SemHonest` | 1 / 1 | 0:02.73 | 6774176 | 0 | 2 | `276183c86d7defa24a7da783449e8c33723c0f4d621771635ef6c422128f0eba` |
| 2008 | `R0P/SemHonest` | 0 / 0 | 0:02.87 | 6808996 | 0 | 2 | `cc9dc6609c862f75e8e9ec97846a3b3996d6f1e377a8a5800190be7fd00486b9` |
| 2009 | `R0P/SemHonest` | 0 / 0 | 0:03.03 | 6805392 | 0 | 3 | `a5c6b2c6da4a66faac7933d49b70d1dcae551ea3819e4f57f3172610d19aae55` |
| 2010 | `R0P/SemHonest` | 1 / 1 | 0:02.92 | 6783872 | 0 | 7 | `440b098b1e18134848dc621ee113b301169e444a9dabd03e6e3bce12afd303fd` |
| 2011 | `R0P/SemHonest` | 0 / 0 | 0:03.26 | 6822628 | 0 | 7 | `160a20301bc4daf1ab4b7ce64650e04e10fa3196157232072eb81716298d6053` |
| 2012 | `R0P/SemHonest` | 1 / 1 | 0:03.07 | 6786864 | 0 | 8 | `4002d918cdb0c0a19fd1fd29244596354b8144f5faed1c3d8e4f4c8b25db2778` |
| 2013 | `R0P/SemHonest` | 1 / 1 | 0:03.09 | 6787632 | 0 | 8 | `4002d918cdb0c0a19fd1fd29244596354b8144f5faed1c3d8e4f4c8b25db2778` |
| 2014 | `R0P/SemHonest` | 1 / 1 | 0:03.08 | 6789520 | 0 | 8 | `214f1e77baf6d332d670b11f7189b19f2842aebba868deae4f36e02c939ba297` |
| 2015 | `R0P/SemHonest` | 1 / 1 | 0:03.11 | 6789860 | 0 | 8 | `25f0a4777cc19b2299585a298a9fb01bd576bc58696fb5cb323e6fc8ab107fe1` |
| 2016 | `R0P/SemHonest` | 0 / 0 | 0:03.22 | 6824840 | 0 | 8 | `0b696d178d81d2835fbe9d48d171caaf5f1763eaa34268c837ae2b989486d654` |
| 2017 | `R0P/SemHonest` | 1 / 1 | 0:03.18 | 6792120 | 0 | 10 | `3ac5fd2a801061fa12b4fa9b595b4dd5d7f153a6b1fcef5744e9b14b03de3036` |
| 2018 | `R0P/SemHonest` | 0 / 0 | 0:03.50 | 6827096 | 0 | 10 | `5b487a9e473678fae2bde6a9f69a003a01eb5d7cbb469a7a47f37a1564e3c8cc` |
| 2019 | `R0P/SemHonest` | 0 / 0 | 0:03.49 | 6827308 | 0 | 12 | `cb6f46b026e1bdf3b0a5ae6c7a937ca9604e2f5474310d6c6b1a7aad2dd33b67` |
| 2020 | `R0P/SemHonest` | 0 / 0 | 0:03.44 | 6826760 | 0 | 13 | `fecde7beb62a8d6e620dc3c84b94df06ba15dff03064e454645ebb559c75fb32` |
| 2021 | `R0P/SemHonest` | 0 / 0 | 0:03.52 | 6830688 | 0 | 14 | `63c890ceebfe82d2ef16e73aed51b4acac0e6bc0af8c5fb3b0d5eca05034234f` |

Source revision(s): `2e002ad58598de04eec8179f73227b6cd2655048`, plus the recorded source snapshots. Failed-attempt audit output is not accepted proof evidence.

### Overnight Step 3 — SemDeg complete

Implemented VDeg with pointwise max/add calculus, scalar/negative/subtraction/power/sum/product/list closure, coordinate functions, and VDeg-to-MLDeg. Proved the source selector product by coordinate reversal, the general rowCode bijection and partition of unity, factorisation at `16*h+l`, and high/low marginal identities with disjoint support vectors. Proved the exact successor claim vector `c.val+1`, current/XOR claim vector 1, equality-value vector 1 and linear pack4 preservation. 2024 checked the generic calculus; 2026 the selector input; 2029 the factorisation/marginals; 2031 the complete input module. Failures were explicit function/index ascriptions, product-sum instantiation, reversed equality predicates, local unfolding and two cast/field annotations. Every retry changed source. 2031 has 47 clean axiom lines, all subsets of the standard three, no warning or error. Reservations were 26+7 GiB for 2022–2024, 24+7 thereafter. The generic successor proof and carry recurrence stayed symbolic; no row or constant-table evaluation.

Host `dombarker@100.108.41.90`; pinned Lean 4.32.0 and existing cache, one Lean job at a time. The existing `run_g15_lake.sh` adapter retains run2’s reservation and scope limits and invokes `lake env lean`: MemoryHigh=5G, MemoryMax=7G, MemorySwapMax=0, 900 s timeout, reservation 24+7 or 26+7 GiB as recorded by each raw host log. No cap increase or dependency build. Raw host artifacts remain in `evidence/`; hash-verified local copies are at `/tmp/r0-g14-overnight-20261009/evidence/`. Evidence files are excluded from commits.

| Attempt | Target | exit / time exit | Wall | Peak RSS KiB | Swaps | Axiom lines | Source SHA-256 |
|---:|---|---:|---:|---:|---:|---:|---|
| 2022 | `R0P/SemDeg` | 1 / 1 | 0:03.03 | 6777620 | 0 | 16 | `3b50b6a8ae9ffaa4ba074b65948684cdbe390ce4b1b9cfc7a01fd4292ccec9ee` |
| 2023 | `R0P/SemDeg` | 1 / 1 | 0:02.99 | 6778100 | 0 | 16 | `9c670a7690203e30d58bbc7ac5b62e29ee1d704863b4d8fa8a320071ecbb7b85` |
| 2024 | `R0P/SemDeg` | 0 / 0 | 0:03.09 | 6812860 | 0 | 16 | `2f511e86971e18325f531a376939df253e147d0990974119ccc7cc58c1b4316f` |
| 2025 | `R0P/SemDeg` | 1 / 1 | 0:03.11 | 6786568 | 0 | 22 | `52cd3b16122b1f45751561c93edff795e74a09d36158a73fa795d2c8019b5e66` |
| 2026 | `R0P/SemDeg` | 0 / 0 | 0:03.35 | 6822652 | 0 | 22 | `a48223a7c9d3ca5a96d9b811342a745773caa4cd9c0520fcaff213be7f248ab0` |
| 2027 | `R0P/SemDeg` | 1 / 1 | 0:03.77 | 6792624 | 0 | 35 | `db78bee88d6dcbd7d62f1aecdd74d23269000be8d34001c54de1d61765c4ae97` |
| 2028 | `R0P/SemDeg` | 1 / 1 | 0:03.62 | 6799276 | 0 | 35 | `815f7d228f5283459018b45bd3239c5ad29ef7cb49f2950d05f7bcc733467916` |
| 2029 | `R0P/SemDeg` | 0 / 0 | 0:03.78 | 6836212 | 0 | 35 | `9c73c7ff496c1ef9b1bc07a8121fcb641dce7539778eae53992e70f868433509` |
| 2030 | `R0P/SemDeg` | 1 / 1 | 0:09.41 | 6834156 | 0 | 47 | `5c5d4fb4007ea232f217305db68fe3537dc6c315d7f33f226b720983bc247cc4` |
| 2031 | `R0P/SemDeg` | 0 / 0 | 0:09.64 | 6874700 | 0 | 47 | `ed059e7d1a94b7f3819398fb7f03762c743ab04d51d0ccd1ba795e8f5d96294e` |

Source revision(s): `c19010238025addba901b094440bfd24538712ce`, plus the recorded source snapshots. Failed-attempt audit output is not accepted proof evidence.

### Overnight G14′ Step 4 — scalar and copy family audit

Value (2038), occupancy (2039), asset (2040), schedule (2041, warning cleanup in 2042), path (2042), digest (2044), and copy (2050) are host-checked at coordinate degree 26. Copy has the stronger bound 10; its active selector has degree one, its mask sum preserves the low-coordinate degree, and patterns are linear. The source scalarLaneAt does not include positiveFamily. Lists, copy masks, pattern descriptors, link registries, and digest targets are treated symbolically. Early 2032–2037 failures were projection elaboration, tactic quotation, and arithmetic-goal plumbing; making honestClaims/openingsOf/selector helpers locally opaque and separating degree construction from the Nat inequality resolved them. 2045 needed let reduction before splitting fixed guards; 2046 is green. No theorem premise or lane statement was weakened. Successful audits contain only propext, Classical.choice, Quot.sound (pointwise_foldl has no axioms); failed audit lines containing sorryAx are retained only as diagnostics.

Host `dombarker@100.108.41.90`; pinned Lean 4.32.0 and existing cache, one Lean job at a time. The existing `run_g15_lake.sh` adapter retains run2’s reservation and scope limits and invokes `lake env lean`: MemoryHigh=5G, MemoryMax=7G, MemorySwapMax=0, 900 s timeout, reservation 24+7 or 26+7 GiB as recorded by each raw host log. No cap increase or dependency build. Raw host artifacts remain in `evidence/`; hash-verified local copies are at `/tmp/r0-g14-overnight-20261009/evidence/`. Evidence files are excluded from commits.

| Attempt | Target | exit / time exit | Wall | Peak RSS KiB | Swaps | Axiom lines | Source SHA-256 |
|---:|---|---:|---:|---:|---:|---:|---|
| 2032 | `R0P/SemDegFamilies` | 1 / 1 | 0:02.82 | 6775164 | 0 | 7 | `852e24f25b7200b6a8539c9da288312a59a77861a8c06070be973a54502afb6a` |
| 2033 | `R0P/SemDegFamilies` | 1 / 1 | 0:03.02 | 6777840 | 0 | 8 | `d1263bb11323ee8baafd7707e1d32d21b4baa71cc8cb1c2ad7d7267ab4d1a8d1` |
| 2034 | `R0P/SemDegFamilies` | 0 / 0 | 0:03.37 | 6811300 | 0 | 11 | `0ed35b4690341628d51e25f089000fae336774c4d812e8ad2e98a06007d93a57` |
| 2035 | `R0P/SemDegFamilies` | 1 / 1 | 0:03.26 | 6785400 | 0 | 13 | `10450a74dbcd6835de226da9ae51236b8ed9fbd94986746fed6615d28e43255c` |
| 2036 | `R0P/SemDegFamilies` | 1 / 1 | 0:09.70 | 6788620 | 0 | 13 | `6c68ba85eead9bd1931783dd50562605a777c73fdf7a7bd98a085bac3ebad57c` |
| 2037 | `R0P/SemDegFamilies` | 1 / 1 | 0:03.36 | 6791252 | 0 | 13 | `5e02332a9f5bf96141ca8a87445f9c23936c56908204f6b9495703a8ce49237c` |
| 2038 | `R0P/SemDegFamilies` | 0 / 0 | 0:03.59 | 6826260 | 0 | 13 | `d436fdaff20774558c27122aba914d4cb4fc729477cc917538a85d74f070d724` |
| 2039 | `R0P/SemDegFamilies` | 0 / 0 | 0:03.93 | 6832668 | 0 | 14 | `e6c1effe63b6a177eaea31b3ccfe2db2c1a118755d47314d67d879972743f34c` |
| 2040 | `R0P/SemDegFamilies` | 0 / 0 | 0:04.66 | 6841404 | 0 | 15 | `8e69685b184a965fa4c02eb71a9d30a7d03f28472e905c0148f0711f014615d9` |
| 2041 | `R0P/SemDegFamilies` | 0 / 0 | 0:09.94 | 6971984 | 0 | 17 | `5e40f398143ce3c09507496b07639c1b42ea73d55ce565639c52500ffe27cee4` |
| 2042 | `R0P/SemDegFamilies` | 0 / 0 | 0:10.34 | 6971692 | 0 | 18 | `2cd817ae9a5df07afd9e48993ea47f2cd6d06aa24a6818812ecb8bee65712159` |
| 2043 | `R0P/SemDegFamilies` | 0 / 0 | 0:10.34 | 6971888 | 0 | 19 | `904b93ceb954db187203b90a3f906f5867329374360b779b7126e2f0fe1afd37` |
| 2044 | `R0P/SemDegFamilies` | 0 / 0 | 0:10.30 | 6973812 | 0 | 21 | `07985384f3daf09eff2f9f980cb373e3f28f690808ebea8b0640f5f8029538d4` |
| 2045 | `R0P/SemDegFamilies` | 1 / 1 | 0:10.17 | 6915568 | 0 | 25 | `b8b65697168fc1d15aee05b66808cbb33bf3f9d1ac01ed007b022a8459700602` |
| 2046 | `R0P/SemDegFamilies` | 0 / 0 | 0:10.53 | 6976212 | 0 | 25 | `8790fd352f1353d5f5fb7a323e3c27a1834330111e0b36c76651dc51fbc91f78` |
| 2047 | `R0P/SemDegFamilies` | 0 / 0 | 0:10.99 | 6978428 | 0 | 26 | `e764c326ae15f0da4c8bb20a32de52a9628e0e060515a068a7b5602cfdcb6410` |
| 2048 | `R0P/SemDegFamilies` | 0 / 0 | 0:10.89 | 6984464 | 0 | 28 | `2afe852b415a487379b9b8b421892f5096a184e0a0ff63d67b2ad05af1458080` |
| 2049 | `R0P/SemDegFamilies` | 0 / 0 | 0:11.40 | 6998592 | 0 | 30 | `cd4d19c59342274d94287acc2427e3987068fb2f362bf15ffd87ff487164c84d` |
| 2050 | `R0P/SemDegFamilies` | 0 / 0 | 0:11.51 | 7000132 | 0 | 32 | `59b1338531e9af0efb58ec27de54716b6e9aa4ceedf284fe3410aa5c9767b231` |

Source revision(s): `692dd8e05dc535d420cbcf1b5a502ca300517cfd`, plus the recorded source snapshots. Failed-attempt audit output is not accepted proof evidence.

### Overnight G14′ Step 4 — Poseidon and all 29 lanes closed

SemDegFamilies now proves vdeg_laneAt for every production lane and every coordinate at bound 26, with no additional premise. The three Poseidon two-round branches have degree 25 (2054); the high and low selector supports are disjoint, so the scalar and packed families have degree 26 (2055). The linear maps were handled symbolically; only the four outputs of the small linear Mat4 expression were selected, and no row range, round constant table, or permutation was evaluated. Attempt 2051 needed an explicit group index for the final linear-map projection; 2052 fixed that and removed unused simp arguments. Full lane assembly passes at 2056, exit 0 with no errors or warnings and 44 axiom lines, all within the standard set. No completeness obstruction was found among the literal lanes. The source was reviewed for forbidden evaluation and added premises before commit.

Host `dombarker@100.108.41.90`; pinned Lean 4.32.0 and existing cache, one Lean job at a time. The existing `run_g15_lake.sh` adapter retains run2’s reservation and scope limits and invokes `lake env lean`: MemoryHigh=5G, MemoryMax=7G, MemorySwapMax=0, 900 s timeout, reservation 24+7 or 26+7 GiB as recorded by each raw host log. No cap increase or dependency build. Raw host artifacts remain in `evidence/`; hash-verified local copies are at `/tmp/r0-g14-overnight-20261009/evidence/`. Evidence files are excluded from commits.

| Attempt | Target | exit / time exit | Wall | Peak RSS KiB | Swaps | Axiom lines | Source SHA-256 |
|---:|---|---:|---:|---:|---:|---:|---|
| 2051 | `R0P/SemDegFamilies` | 1 / 1 | 0:11.48 | 6939040 | 0 | 34 | `72ec5a9633d1aed5a7dd6fa9359e725ffa7e2850eebec7c4f803476af8d913f0` |
| 2052 | `R0P/SemDegFamilies` | 0 / 0 | 0:11.58 | 7000748 | 0 | 34 | `a7f12bf9cc511186e4b59edd302277a275941796a909707cdb61e45561c453c3` |
| 2053 | `R0P/SemDegFamilies` | 0 / 0 | 0:11.86 | 7001816 | 0 | 37 | `359cdd212edf4af0aab5dc296138b3b7388a68bb63a1eaeef3051fbf39d3e317` |
| 2054 | `R0P/SemDegFamilies` | 0 / 0 | 0:12.22 | 6993968 | 0 | 40 | `8c833325f463ac64fd46b4a0fcdc0ae46958bf9284d508775c9998af1b52185e` |
| 2055 | `R0P/SemDegFamilies` | 0 / 0 | 0:12.77 | 7002972 | 0 | 42 | `476e1ee560b725aebc3ee430e2f92f6f7286853b25819f7e4223410aa67bb3c2` |
| 2056 | `R0P/SemDegFamilies` | 0 / 0 | 0:13.15 | 7002080 | 0 | 44 | `60daa294e557252938f4d87fb9eb93df7aca5eff51795abf595c140a3b15c3e1` |

Source revision(s): `692dd8e05dc535d420cbcf1b5a502ca300517cfd`, plus the recorded source snapshots. Failed-attempt audit output is not accepted proof evidence.

### Overnight G14′ Step 5 — unconditional VirtualDeg

SemVirtualDeg proves the literal terminal and virtualPoly coordinate bounds at 27, then applies vdeg_mlDeg and SemBadSets.mlDeg_indDeg to discharge the original VirtualDeg Prop. Equality weighting contributes one to the audited lane bound 26; the honest helper and inactive-copy term are bounded using the proved activeAt degree one. Attempt 2057 passes on its first focused run with no errors or warnings; all three axiom lines are [propext, Classical.choice, Quot.sound]. No premise was added.

Host `dombarker@100.108.41.90`; pinned Lean 4.32.0 and existing cache, one Lean job at a time. The existing `run_g15_lake.sh` adapter retains run2’s reservation and scope limits and invokes `lake env lean`: MemoryHigh=5G, MemoryMax=7G, MemorySwapMax=0, 900 s timeout, reservation 24+7 or 26+7 GiB as recorded by each raw host log. No cap increase or dependency build. Raw host artifacts remain in `evidence/`; hash-verified local copies are at `/tmp/r0-g14-overnight-20261009/evidence/`. Evidence files are excluded from commits.

| Attempt | Target | exit / time exit | Wall | Peak RSS KiB | Swaps | Axiom lines | Source SHA-256 |
|---:|---|---:|---:|---:|---:|---:|---|
| 2057 | `R0P/SemVirtualDeg` | 0 / 0 | 0:03.07 | 6813452 | 0 | 3 | `c7660c31f4d9c72d6b8b654450ffb6d4e6dc180de99b158c84e79d4f4874f4ee` |

Source revision(s): `278fd3cd7f38dcf9a52ac5761ce7f522ac97d0f6`, plus the recorded source snapshots. Failed-attempt audit output is not accepted proof evidence.

### Overnight G14′ Step 6 / G15 — D3 closed

The unchanged D3 target from diagnostic 2124 now closes in 2125 by supplying honestRows, virtualDeg, and checksAccept; no goals remain. SemD3Glue.d3 now calls these proofs internally and has none of the three G14 Props as hypotheses. Its characteristic and concrete gamma-decoder identity parameters are unchanged, and SemStatement.Obligations is unchanged. The complete focused SemD3Glue host run 2126 passes with no errors or warnings and 55 standard axiom lines. In particular: 'R0P.SemD3Glue.d3' depends on axioms: [propext, Classical.choice, Quot.sound]. The independent obligation diagnostic has the same axiom set. This closes the requested mixed-protocol D3 component. Each preceding bridge module was committed and pushed after its successful focused run. Only Lean sources and LOG are included; evidence snapshots remain uncommitted.

Host `dombarker@100.108.41.90`; pinned Lean 4.32.0 and existing cache, one Lean job at a time. The existing `run_g15_lake.sh` adapter retains run2’s reservation and scope limits and invokes `lake env lean`: MemoryHigh=5G, MemoryMax=7G, MemorySwapMax=0, 900 s timeout, reservation 24+7 or 26+7 GiB as recorded by each raw host log. No cap increase or dependency build. Raw host artifacts remain in `evidence/`; hash-verified local copies are at `/tmp/r0-g14-overnight-20261009/evidence/`. Evidence files are excluded from commits.

| Attempt | Target | exit / time exit | Wall | Peak RSS KiB | Swaps | Axiom lines | Source SHA-256 |
|---:|---|---:|---:|---:|---:|---:|---|
| 2125 | `R0P/D3ObligationCheck` | 0 / 0 | 0:03.05 | 6821920 | 0 | 1 | `d451e44571a2b1c6c99e268cf184e8cd64f7392bf40dde5b703f5d8f4d39e78d` |
| 2126 | `R0P/SemD3Glue` | 0 / 0 | 0:21.78 | 6939620 | 0 | 55 | `26f6c39987de422e0b38779db55e8c26ce728d4c6a01a9061ff9f4157b16bf17` |

Source revision(s): `aee0c74d9a69ffdfe99431c966edf89242f53f9d`, plus the recorded source snapshots. Failed-attempt audit output is not accepted proof evidence.

### G16 continuation after G15 closure — prime, circle, and opening sub-bounds

Resumed the previously authorized G16 job only after D3 was green and pushed. The canonical-prime bridge P_eq compiled first in isolation at 2210 using the requested norm_num proof. The existing opening draft was checked at 2211–2213: q22 needed the forward challenge rewrite, the explicit round-30 branch, and explicit observer arguments to chainS_independentMean; 2213 passes the semantic, four field-opening, and q22 sub-bounds. Row 24 passes at 2214 using circleSample_z0_mass; row 25 passes at 2216 using circleSample_z1_mass. Both bounds use P_eq to obtain the exact 2/P² budget. Attempt 2215 reached a simplifier timeout while unnecessarily expanding a prefix in the missing-previous-challenge case; 2216 uses the existing no-flip lemma directly with an atomic hypothesis and the generic zero-mean lemma. The cap was unchanged. Concrete bad predicates remain existing defs, and no filter/cardinality or DecidableEq unification was introduced. Successful axiom audits use only the standard three; failed outputs are diagnostic only. Full 31-row assembly follows only after each arbitrary-message sub-bound is checked.

Host `dombarker@100.108.41.90`; pinned Lean 4.32.0 and existing cache, one Lean job at a time. The existing `run_g15_lake.sh` adapter retains run2’s reservation and scope limits and invokes `lake env lean`: MemoryHigh=5G, MemoryMax=7G, MemorySwapMax=0, 900 s timeout, reservation 24+7 or 26+7 GiB as recorded by each raw host log. No cap increase or dependency build. Raw host artifacts remain in `evidence/`; hash-verified local copies are at `/tmp/r0-g14-overnight-20261009/evidence/`. Evidence files are excluded from commits.

| Attempt | Target | exit / time exit | Wall | Peak RSS KiB | Swaps | Axiom lines | Source SHA-256 |
|---:|---|---:|---:|---:|---:|---:|---|
| 2210 | `R0P/SemD2Prime` | 0 / 0 | 0:02.85 | 6811536 | 0 | 1 | `a4ae4410a15c985fc7280f58dfdc0f4ce32b9b64c9ce9edef10a0dd5273db82a` |
| 2211 | `R0P/SemD2Glue` | 1 / 1 | 0:07.34 | 6821552 | 0 | 9 | `cf446ca0547237dc38d09180482bd4bd6308019bd4b89e50aa6eb2c024416c01` |
| 2212 | `R0P/SemD2Glue` | 1 / 1 | 0:07.47 | 6822760 | 0 | 9 | `2e19d3f1e158c41eaa52df885b54143bfcb0cfa8b951176ca608634c786a8d91` |
| 2213 | `R0P/SemD2Glue` | 0 / 0 | 0:07.96 | 6859936 | 0 | 9 | `9f814f34bf16c1a9eb50fad68e64dc53d382e46d1245dac1545084789a5bf4d2` |
| 2214 | `R0P/SemD2Glue` | 0 / 0 | 0:11.19 | 6873652 | 0 | 17 | `cf7312df06420a1317c06adc3f8baaf7e71837c9f26ce911d0c0207fe15a4ad2` |
| 2215 | `R0P/SemD2Glue` | 1 / 1 | 0:21.27 | 6847148 | 0 | 21 | `91f1c695b7384410501129a45be425d5a25a27cfd4d420f16254fcd7c6c6a781` |
| 2216 | `R0P/SemD2Glue` | 0 / 0 | 0:13.40 | 6883220 | 0 | 21 | `47f37bee1757306859250308649a86f6cd78ecc68ddeb027f1b1c77add40ae92` |

Source revision(s): `da49d26614e991db31fdc6d615ebd07285d0f8e3`, plus the recorded source snapshots. Failed-attempt audit output is not accepted proof evidence.

### G16 — full 31-row D2 closed

Every sub-bound was green before assembly: semantic and parsed opening rows at 2213, circle row 24 at 2214 (lint cleanup included in 2216), circle row 25 at 2216, arbitrary-message field rows at 2218, and arbitrary-message q22 at 2219. Attempt 2217 removed four no-op dsimp calls. Attempt 2220 exposed an assembly-only substitution issue: subst i chose the prefix-round equality rather than the desired local row equation. Attempt 2221 rewrites the selected row equations explicitly and transports hround by transitivity. It proves FS2.D2 for all 31 rows of combinedProtocol with combinedD2Budget: the lead-authorized ×100 semantic table, 2/P² for each circle row, and the existing opening slack bounds. The four source-fixed sigma identity clauses are unchanged from the draft; no probability, degree, candidate, or parser premise was added. The final run has exit 0, no errors or warnings, 28 axiom audits, and no sorryAx. In particular: 'R0P.SemSource.combinedProtocol_D2' depends on axioms: [propext, Classical.choice, Quot.sound]. Source and final diff were reviewed; this closes Job B. Only SemD2Glue.lean and LOG are committed, with evidence excluded.

Host `dombarker@100.108.41.90`; pinned Lean 4.32.0 and existing cache, one Lean job at a time. The existing `run_g15_lake.sh` adapter retains run2’s reservation and scope limits and invokes `lake env lean`: MemoryHigh=5G, MemoryMax=7G, MemorySwapMax=0, 900 s timeout, reservation 24+7 or 26+7 GiB as recorded by each raw host log. No cap increase or dependency build. Raw host artifacts remain in `evidence/`; hash-verified local copies are at `/tmp/r0-g14-overnight-20261009/evidence/`. Evidence files are excluded from commits.

| Attempt | Target | exit / time exit | Wall | Peak RSS KiB | Swaps | Axiom lines | Source SHA-256 |
|---:|---|---:|---:|---:|---:|---:|---|
| 2217 | `R0P/SemD2Glue` | 1 / 1 | 0:14.31 | 6845860 | 0 | 23 | `6658d9af642a46c90e572425fbcd90f522e080f720f29c47146fb641cb8faa4f` |
| 2218 | `R0P/SemD2Glue` | 0 / 0 | 0:14.73 | 6886916 | 0 | 23 | `24e96da1ee921f971bf6d28ae20a79f4f147fe4586ce61131247bf69ef5887f9` |
| 2219 | `R0P/SemD2Glue` | 0 / 0 | 0:16.01 | 6892892 | 0 | 26 | `250d496bbabd1c857689f3fde1b95841174f6353a98faf7bac909f46bca17972` |
| 2220 | `R0P/SemD2Glue` | 1 / 1 | 0:16.48 | 6857552 | 0 | 28 | `7bf928f53d4577b19abc57025a62ed6c38f32bcbf0c499ffe71b69763d2d5997` |
| 2221 | `R0P/SemD2Glue` | 0 / 0 | 0:16.99 | 6901280 | 0 | 28 | `71de3ca82cc1329e598d87b50a2e985115bd626db36cda1aedef487d2e71dc46` |

Source revision(s): `da49d26614e991db31fdc6d615ebd07285d0f8e3`, plus the recorded source snapshots. Failed-attempt audit output is not accepted proof evidence.

## Lead review of the overnight G14′/G15/G16 closure; G20 decision

Reviewed commits `eb8df067e`–`1f97f75c4` (2026-10-09). Checked against
host evidence (not Codex's report): each committed source's SHA-256 equals
`sha-N.txt` of its accepted attempt (2006, 2021, 2031, 2056, 2057, 2126,
2221); every `depends on axioms` line in those logs is a subset of
`propext, Classical.choice, Quot.sound`; no `sorryAx`, no `error`; no
`decide`/`native_decide`/`maxRecDepth`/`maxHeartbeats`; the only
`fin_cases` are over `Fin 3`/`Fin 4`; `Finset.univ` occurs only inside
symbolic `vdeg_sum`/`vdeg_prod` applications. Accepted:

- `SemAccept.checksAccept`, `SemHonest.honestRows`, `SemVirtualDeg.virtualDeg`
  discharge the three G14′ Props with no premise. The degree audit
  (`SemDeg.VDeg`, coordinate-vector degrees with the high/low selector
  factorisation `selAt_g2Row`, `eqHigh_sum`, `eqLow_sum`) is the
  coordinate-sensitive criterion the lead prescribed; all 29 lanes are at
  bound 26, the terminal at 27. No completeness finding against the
  source's degree constant.
- `SemD3Glue.d3`: `FS2.D3 (combinedProtocol B p msg decode) (duplexRows B budget) (verifier … (combinedDecision B))`
  with premises `[CharP SemE prime]`, `prime = 2^31-1`, and
  `hσ26 : ∀ s, p.σ 26 s = .opening (σQ 0 s)`. These are instance facts
  (the field's characteristic; the source-fixed decoder of the first
  opening row), not weakenings. `SemStatement.Obligations` unchanged.
- `SemD2Glue.combinedProtocol_D2`: `FS2.D2` for all 31 rows under
  `combinedD2Budget` (rows 0–23: `(1+δQ)·100·semRoundBudget i / P⁴`;
  rows 24–25: `2/P²`; rows 26–30: the existing slack rows), with the four
  σ-decoder identities as premises. Budgets are the lead-authorised ones.

D1 is definitional for the semantic source: `extract s x T = none` is
`¬ ∃ w, paymentWitness x w`, and `doomed s (emptyPrefix x) T` is that
conjunct together with `¬ hitFrom s x [] []` (= `¬ False`).

What remains for the theorem43 instance (`R0C.V3.theorem43`, Gen.lean:251):
`ChainDensity3` and `Inj3.decodes` for the combined protocol, i.e. the
31-round analogue of `R0C.V3.DQ.decQ` with `chainDensityQ` and `decodesQ`.
The FS2 decoder infrastructure (`parseAbsorb`, `walk`, `Rec`,
`completePrefix`, `Coll`, `coll_mass`, `absC`) is generic in the message
and challenge types; only `DuplexQ`/`DQChain`/`DQDecodes`/`DuplexQDensity`
are specialised to R0's five rounds (`i < 4` one-block rows, chain at 4,
`recs.length < 5`, `out4`). Decision (G20): Codex ports those four modules
into the job directory for the combined types (`Msg SemE SemE (SemMsg SemE)`,
`Duplex.Chal (Chal SemE SemE)`, 30 one-block rows, chain at row 30 with
`openingChallenge ∘ out4`, `recs.length < 31`), proving chain density from
`combinedProtocol_D2` row by row (one-block rows by the single-squeeze
mean, row 30 by `Q22.chainE`), and assembles `combined_fiat_shamir` via
`theorem43` with `Inj3 := ⟨Coll p Qtot, coll_mass …, decodes⟩`. The
`CharP SemE (2^31-1)` premise is discharged by the lead
(`charP_of_injective_algebraMap` from the existing
`Algebra (ZMod AspisCircleGroupOrder.P) WideExact` instance). The closed
form of `maxErr combinedD2Budget 31` is lead accounting (G21), after G20.

## Lead: `SemCharP.lean` — the characteristic premise discharged

`semE_charP : CharP SemE AspisCircleGroupOrder.P` by
`charP_of_injective_algebraMap` from the `Algebra (ZMod P) SemE` instance
`TypedContext` already uses; `semE_prime_eq : P = 2^31 - 1` by `norm_num`.
Host attempt 672 (`run2.sh 672 R0P/SemCharP 7000 7`): `exit=0`, wall
0:02.86, peak RSS 6,827,176 KiB, swaps 0, no errors or warnings, axioms
standard. With these, `SemD3Glue.d3` is applicable at
`prime := AspisCircleGroupOrder.P` with `hprime := semE_prime_eq`.

### G20 — combined decoder

Ported the completing decoder to the mixed message/challenge types: single-pair rows below 30 and the literal eight-pair q22 output at row 30, with a 31-row guard. The generic chain law and the equality with the opening-parameter chain are proved symbolically. The decoder definition needs no round-count premise; consumers retain p.rounds = 31 for the backward walk. Host 2600 is exit 0, no errors or warnings, and all three audited declarations use only propext, Classical.choice, Quot.sound. R0C and maxErr accounting are unchanged.

Host `dombarker@100.108.41.90`; pinned Lean 4.32.0 and existing cache, one Lean job at a time. The existing `run_g15_lake.sh` adapter retains run2’s reservation and scope limits and invokes `lake env lean`: MemoryHigh=5G, MemoryMax=7G, MemorySwapMax=0, 900 s timeout, reservation 24+7 or 26+7 GiB as recorded by each raw host log. No cap increase or dependency build. Raw host artifacts remain in `evidence/`; hash-verified local copies are at `/tmp/r0-g20-20261009/evidence/`. Evidence files are excluded from commits.

| Attempt | Target | exit / time exit | Wall | Peak RSS KiB | Swaps | Axiom lines | Source SHA-256 |
|---:|---|---:|---:|---:|---:|---:|---|
| 2600 | `R0P/SemDuplexDecoder` | 0 / 0 | 0:04.56 | 6834532 | 0 | 3 | `cc8dc9b73d6f98a43ba8a41771e1cf356cac5ad3a7e87b062f031e4e0ba86236` |

Source revision(s): `5f4ad4aee9d14cd7994121845407f839d0c4a146`, plus the recorded source snapshots. Failed-attempt audit output is not accepted proof evidence.

### G20 — combined chain density

Proved the flip-to-source-roundBad bridge and an exact equality between the completing sampler law and the combined sampler law. For rows below 30 this uses the single-squeeze mean; the final row uses Q22.chainE, with the absorb state still averaged. Splitting off earlier missing squeezes then applies the existing full combinedProtocol_D2 with exactly its four sigma identities. Attempt 2601 checks the law first; 2602 exposed only an unspecified existential table type, fixed by its explicit annotation in 2603. Final exit 0, no errors or warnings, all four axiom audits standard. No density premise, concrete finite enumeration, or accounting change was introduced.

Host `dombarker@100.108.41.90`; pinned Lean 4.32.0 and existing cache, one Lean job at a time. The existing `run_g15_lake.sh` adapter retains run2’s reservation and scope limits and invokes `lake env lean`: MemoryHigh=5G, MemoryMax=7G, MemorySwapMax=0, 900 s timeout, reservation 24+7 or 26+7 GiB as recorded by each raw host log. No cap increase or dependency build. Raw host artifacts remain in `evidence/`; hash-verified local copies are at `/tmp/r0-g20-20261009/evidence/`. Evidence files are excluded from commits.

| Attempt | Target | exit / time exit | Wall | Peak RSS KiB | Swaps | Axiom lines | Source SHA-256 |
|---:|---|---:|---:|---:|---:|---:|---|
| 2601 | `R0P/SemDuplexDensity` | 0 / 0 | 0:03.53 | 6833764 | 0 | 2 | `93d74fbe77c1aecd90e33a2879a37358a0a83bdafd64e51189a4f17a39ea28a3` |
| 2602 | `R0P/SemDuplexDensity` | 1 / 1 | 0:04.55 | 6810324 | 0 | 4 | `e6e9059437f5a5ec99c49059e2939130d58f42a0df7ad07ba9f3b571a859cb25` |
| 2603 | `R0P/SemDuplexDensity` | 0 / 0 | 0:05.10 | 6847344 | 0 | 4 | `64562fc7187cfe8e64c1face96c195f6beeb2446714a02239f4c6c9587bd5b72` |

Source revision(s): `da1caa9ef36b9064244e2e791a7ba9601128a422`, plus the recorded source snapshots. Failed-attempt audit output is not accepted proof evidence.

### G20 — combined decoder correctness

Ported DQChain and DQDecodes into SemDuplexDecodes, retaining the generic FS2 collision and backward-walk lemmas. The mixed transcript agrees with the generic duplex through prefix 30; rows below 30 use one pair and row 30 reads all eight opening pairs. combinedDecodes proves exactly the Inj3 output/follow shape from hr31, the total-read cap and absence of Coll. Focused chain/transcript checks passed at 2605 after replacing an over-eager congr tactic (2604); ordering helpers passed at 2606. Full assembly passed at 2607, with unused simp arguments cleaned in 2608. Final exit 0, no errors or warnings; all nine axiom lines use only subsets of propext, Classical.choice, Quot.sound. No premise was added or weakened, and R0C is untouched.

Host `dombarker@100.108.41.90`; pinned Lean 4.32.0 and existing cache, one Lean job at a time. The existing `run_g15_lake.sh` adapter retains run2’s reservation and scope limits and invokes `lake env lean`: MemoryHigh=5G, MemoryMax=7G, MemorySwapMax=0, 900 s timeout, reservation 24+7 or 26+7 GiB as recorded by each raw host log. No cap increase or dependency build. Raw host artifacts remain in `evidence/`; hash-verified local copies are at `/tmp/r0-g20-20261009/evidence/`. Evidence files are excluded from commits.

| Attempt | Target | exit / time exit | Wall | Peak RSS KiB | Swaps | Axiom lines | Source SHA-256 |
|---:|---|---:|---:|---:|---:|---:|---|
| 2604 | `R0P/SemDuplexDecodes` | 1 / 1 | 0:07.52 | 6815804 | 0 | 5 | `98203be1630b580e325fdb0f0851d66a3b5a0070fb755bfc9064a82d9830ac3b` |
| 2605 | `R0P/SemDuplexDecodes` | 0 / 0 | 0:07.69 | 6851836 | 0 | 5 | `07e99e3c016baca2b651ecb624806f538241ad0d887e4bfe1cea705427a8f7b6` |
| 2606 | `R0P/SemDuplexDecodes` | 0 / 0 | 0:08.79 | 6856560 | 0 | 7 | `f6e28e41fec67cdb74f208ba0705cc502d7fd33447211c861600d5ee6261a4c1` |
| 2607 | `R0P/SemDuplexDecodes` | 0 / 0 | 0:11.94 | 6901828 | 0 | 9 | `3b29bf9dff46bfc983831d2868056f46767d4faf5a3077cc2ef86de52500c1c2` |
| 2608 | `R0P/SemDuplexDecodes` | 0 / 0 | 0:11.35 | 6910704 | 0 | 9 | `f885ebfe138c092810c4bb0bd39d4dc7567a4aa4f93148a944edb06c421aa7d6` |

Source revision(s): `c590062644bba3ce921614a0aa27ef9c645b1321`, plus the recorded source snapshots. Failed-attempt audit output is not accepted proof evidence.

### G20 — theorem43 instance closed

SemFiatShamir proves combinedChainsRead, combinedReadsChains, and the definitional combinedD1 (focused attempt 2609), then combined_fiat_shamir via R0C.V3.theorem43 (2610). The theorem uses the requested none decoder field, hr31, the four unchanged source sigma identities, and the total distinct-first-read bound. D3 is instantiated at AspisCircleGroupOrder.P using SemCharP.semE_prime_eq; hσopen 0 is definitionally the required sigma-26 identity. Inj3 uses Coll, coll_mass, and combinedDecodes. The conclusion is exactly Qtot * maxErr combinedD2Budget 31 + κ Qtot; the G21 closed form is untouched. Final exit 0, no errors or warnings, all four axiom lines are [propext, Classical.choice, Quot.sound]. Final source files were hash-matched to the successful host snapshots (2600, 2603, 2608, 2610), and reviewed for admitted proofs, forbidden finite evaluation, and altered premises. No obstruction remains in G20. Each module is committed and pushed separately with sources plus LOG only; R0C and evidence are excluded.

Host `dombarker@100.108.41.90`; pinned Lean 4.32.0 and existing cache, one Lean job at a time. The existing `run_g15_lake.sh` adapter retains run2’s reservation and scope limits and invokes `lake env lean`: MemoryHigh=5G, MemoryMax=7G, MemorySwapMax=0, 900 s timeout, reservation 24+7 or 26+7 GiB as recorded by each raw host log. No cap increase or dependency build. Raw host artifacts remain in `evidence/`; hash-verified local copies are at `/tmp/r0-g20-20261009/evidence/`. Evidence files are excluded from commits.

| Attempt | Target | exit / time exit | Wall | Peak RSS KiB | Swaps | Axiom lines | Source SHA-256 |
|---:|---|---:|---:|---:|---:|---:|---|
| 2609 | `R0P/SemFiatShamir` | 0 / 0 | 0:03.83 | 6832584 | 0 | 3 | `8ece4f13312d662065385a939c795cd716cca08b1cae724a8ce7eff5a9cf1830` |
| 2610 | `R0P/SemFiatShamir` | 0 / 0 | 0:05.50 | 6842688 | 0 | 4 | `96b7f16931cb8ceedfdaaeca19182fa8311671b351a943410b1b6eba0e4917e0` |

Source revision(s): `6e15b229b6af6a7a530f05b4c51ed8098631d18e`, plus the recorded source snapshots. Failed-attempt audit output is not accepted proof evidence.

## Lead: G20 accepted; G21 accounting; G22 decision (circle fallback point)

G20 (`da1caa9ef`–`6a9702365`) verified against host evidence (SHA match for
2600/2603/2608/2610, no `sorryAx`, standard axioms, no errors/warnings, no
forbidden constructs). `combined_fiat_shamir` has exactly the intended
premises: `p.rounds = 31`, the four σ-decoder identities, the query bound.

G21 accounting of `maxErr combinedD2Budget 31`:
- rows 0–23: `(1+δQ)·100·semRoundBudget i / P⁴`, max at row 0
  (`2176` → `217600·(1+δQ)/P⁴` ≈ 2^-106.3);
- rows 24–25: `2/P²` ≈ 2^-61;
- rows 26–30: `(1+δ0)·R0FS.ε i`, max the q22 row ≈ 2^-105.1
  (`SlackBits.max_error_query`).
So the maximum is the circle rows' `2/P²`, and the final bound would be
`Q·2/P² + 2Q²/2^256`. That term is entirely the one-block sentinel model
of the source's rejection loop (a CM31 draw, probability `1/P²`, counted
as bad), not an attack.

Decision (G22). The reference verifier is ours to fix; the retry loop buys
nothing and costs either this 2^-61 term or a variable-length decoder.
The reference sampler becomes: squeeze `t`; if `t.im ≠ 0` the point is
`embedCirclePoint (point t)`; otherwise a **fixed fallback point**, `f0`
for row 24 and `f1 ≠ f0` for row 25, both non-base-rational (embedded
images of fixed parameters). Bad sets become: row 24 `z0Bad z0 :=
BaseRational z0 ∨ z0 = f1`; row 25 `z1Bad z0 z1 := z1 = z0 ∨ BaseRational
z1` as now. Then row 24 is bad only on the ≤ 1 parameter with
`circleSampleParameter t = f1` (the rejected set maps to `f0 ≠ f1`, never
rational): budget `1/P⁴`. For a doomed prefix at row 25, `z0 ≠ f1`, so
row 25 is bad only on the ≤ 1-parameter fiber of `z0`: budget `1/P⁴`.
`maxErr` is then the q22 row, `(1+δ0)·C(9557,22)/C(262144,22)` ≈ 2^-105.1.
Required source change (reference Rust, `transcript.rs:453–465`): replace
the retry with the fallback; recorded here, to be applied with the lead's
sign-off before the refinement job. `rowBudget` for circle rows in
`R0C.SemStatement` becomes `1/P⁴`; `z0Bad` gains the `= f1` disjunct.

### G22 — fallback and fiber checkpoint; ideal mass obstruction

Added circleFallback0/1 from the explicit QM31 parameters (0,1)/(1,1), proved their non-rationality and inequality by symbolic parameter recovery, and defined the row-specific circleSampleParameter0/1 and circleSample0/1. Concrete bad predicates remain defs; circleBad0_card and circleBad1_card are at most one using the generic atomic-predicate cardinality lemma. circleSample0_bad_iff identifies the first-row event exactly with qm31Sample = circleFallbackParameter1. The requested 1/P^4 mass target is not accepted: the existing sampler is modulo reduction and has only the (1+deltaQ)/P^4 law. In particular the selected fallback1 rank P^2+1 is below 256^32 mod P^4 and has an overweight fiber; a focused obstruction proof follows. The accepted G20 sentinel interfaces are retained while this finding is reviewed, so the checkpoint does not silently change the proved G20 protocol. Attempts 2700/2701 exposed concrete point reduction during unification; 2702 moved recovery into a generic symbolic helper without raising any cap. Samplers and cardinalities pass at 2703, exit 0, no errors/warnings, all 36 axiom lines standard. No 1/P^4 mass theorem or changed R0C budget is asserted.

Host `dombarker@100.108.41.90`; pinned Lean 4.32.0 and existing cache, one Lean job at a time. The existing `run_g15_lake.sh` adapter retains run2’s reservation and scope limits and invokes `lake env lean`: MemoryHigh=5G, MemoryMax=7G, MemorySwapMax=0, 900 s timeout, reservation 24+7 or 26+7 GiB as recorded by each raw host log. No cap increase or dependency build. Raw host artifacts remain in `evidence/`; hash-verified local copies are at `/tmp/r0-g22-20261009/evidence/`. Evidence files are excluded from commits.

| Attempt | Target | exit / time exit | Wall | Peak RSS KiB | Swaps | Axiom lines | Source SHA-256 |
|---:|---|---:|---:|---:|---:|---:|---|
| 2700 | `R0P/CircleSampler` | 1 / 1 | 0:11.89 | 6812668 | 0 | 31 | `5fa646e37ee392a69bb2e1a54e7be4f73b189f052390ca991f153eb29aaf6348` |
| 2701 | `R0P/CircleSampler` | 1 / 1 | 0:11.91 | 6812204 | 0 | 31 | `ce8fb9d03aac7874218f75393a26e2bad04a71ae19ce021b7f4667b235180d5a` |
| 2702 | `R0P/CircleSampler` | 0 / 0 | 0:14.67 | 6844708 | 0 | 31 | `bfdc713c5186a133a13157b77370723f79f56ffff0707a4d5bcb9b8e0454f707` |
| 2703 | `R0P/CircleSampler` | 0 / 0 | 0:18.08 | 6848900 | 0 | 36 | `6a702fddefcd2f74ee883e34e46c8d32dcdd9af8a505869ef58b05e5407a00cc` |

Source revision(s): `d7ce72ab61862d8611afa6bd4d1d9dd8d98410d7`, plus the recorded source snapshots. Failed-attempt audit output is not accepted proof evidence.

### G22 — formal mass obstruction; stop before R0C handoff, G21 and G23

CircleMassObstruction proves not_circleSample0_mass and circleSample1_mass_counterexample, the latter including circleFallback0 != circleFallback1. The generic proof injects Fin (B/n+1) into a heavy modulo fiber, transfers the count across the input/output equivalences, and proves its mass strictly exceeds 1/n. It is checked before the concrete fallback ranks. The rank computation is symbolic over four limbs; the only numeric checks compare P^2 and P^2+1 with 256^32 mod P^4. There is no finite enumeration, decide, native_decide, or axiom addition. Attempt 2704 had a looping generic modulo simp and a multiplication normalization error; 2705 needed zero_mod; 2706 passes the generic count. Attempt 2707 needed explicit M31 projections for the rank; 2708 proves the first-row obstruction. The full two-row obstruction passes at 2709, exit 0, no errors/warnings, all 12 axiom lines standard. The requested mass statements have not been weakened or replaced by slack versions. R0C, SemD2Glue and combinedD2Budget are unchanged. No 28xx or 29xx attempt or final manifest replay was launched, because the requested G22 bounds are false and the source/budget decision is pending.

Host `dombarker@100.108.41.90`; pinned Lean 4.32.0 and existing cache, one Lean job at a time. The existing `run_g15_lake.sh` adapter retains run2’s reservation and scope limits and invokes `lake env lean`: MemoryHigh=5G, MemoryMax=7G, MemorySwapMax=0, 900 s timeout, reservation 24+7 or 26+7 GiB as recorded by each raw host log. No cap increase or dependency build. Raw host artifacts remain in `evidence/`; hash-verified local copies are at `/tmp/r0-g22-20261009/evidence/`. Evidence files are excluded from commits.

| Attempt | Target | exit / time exit | Wall | Peak RSS KiB | Swaps | Axiom lines | Source SHA-256 |
|---:|---|---:|---:|---:|---:|---:|---|
| 2704 | `R0P/CircleMassObstruction` | 1 / 1 | 0:04.21 | 6792612 | 0 | 3 | `f9cc97a9d9f57b8465478079bc376ffdc2ace98e956cb0392c3b766db3c60a74` |
| 2705 | `R0P/CircleMassObstruction` | 1 / 1 | 0:03.93 | 6755972 | 0 | 3 | `c81fb4e62f7d283bbfba9d8d851c2073c5bcfbee65b93607f900608061db7ac9` |
| 2706 | `R0P/CircleMassObstruction` | 0 / 0 | 0:03.80 | 6796644 | 0 | 3 | `f948e8a3dcd5f66fd87e8cbde9b2cd2cd50d2bef44aba09342e850966de2d83b` |
| 2707 | `R0P/CircleMassObstruction` | 1 / 1 | 0:03.76 | 6789824 | 0 | 8 | `f6d9bce3dfa5430eb613535f8db2e36dcb7d5ab4da8568f63d8e1d3e6de624bc` |
| 2708 | `R0P/CircleMassObstruction` | 0 / 0 | 0:03.72 | 6820924 | 0 | 8 | `508ebaffcc4aa655f796f0ee20a63a03eff507e3622b114bf721a36037eab9e1` |
| 2709 | `R0P/CircleMassObstruction` | 0 / 0 | 0:03.84 | 6823284 | 0 | 12 | `7bb9a6f7d7d6e73aca67b3073e7ae01cbe8cf8d9a6fa2da67dcffee1c6710511` |

Source revision(s): `437c018e58212e61be24702235ca150221f4e938`, plus the recorded source snapshots. Failed-attempt audit output is not accepted proof evidence.

#### Exact stopped obligations

The requested goals, with `P := AspisV5ComponentCQM31TowerExact.P`, are:

```lean
⊢ mean (fun s : State => indicator (z0Bad' (circleSample0 s))) ≤ 1 / (P ^ 4 : ℚ)

z0 : Point WideExact
hz0 : z0 ≠ circleFallback1
⊢ mean (fun s : State => indicator (z1Bad z0 (circleSample1 s))) ≤ 1 / (P ^ 4 : ℚ)
```

The first goal is negated by `R0P.CircleMassObstruction.not_circleSample0_mass`.
For the second, `circleSample1_mass_counterexample` supplies `z0 = circleFallback0`,
proves the stated `hz0`, and negates the goal. These are checked theorems, not
failure-to-find-proof claims.

Write `N = P^4`, `B = 256^32`, `q = B / N`, `r = B % N`. Here
`r = 141976867060278866133163874180352`, while the two accepted fallback
parameter ranks are `P^2 = 4611686014132420609` and
`P^2+1 = 4611686014132420610`. Both are below `r`. Their masses are at least
`(q+1)/B > 1/N` by the generic heavy-fiber proof. Replacing rejected parameters
with a fallback does not change these accepted-parameter fibers.

The sampler in `SemD2.lean:183` is modulo reduction, not uniform QM31 sampling.
Its existing law is `qm31Sample_mass_slack`, with `(1+deltaQ)/P^4`.
Retaining that small slack, or changing the sampler, requires a lead decision;
neither alternative is silently installed in the requested theorem or budget.
The `1/P^4` rowBudget edit requested in G22 therefore cannot be supplied as a
sound integration patch for the current sampler.

#### Exact unapplied R0C event-interface diff

This is the event/interface portion only, for lead review after the mass/budget
decision. It has **not** been applied or host-checked. The current two circle
budgets are deliberately unchanged. A concrete `Point WideExact` cannot serve
the generic `Point K` interface directly, and `CircleRows` already imports
`SemStatement`; importing CircleRows back into SemStatement would form a cycle.
Instead, keep the proved concrete fallback in `R0P.CircleSampler` and carry it
as `SourceData.circleFallback1 : Point K` (data, not an extra proof premise).
The subsequent job-directory integration would import CircleSampler in
SemD3Glue and fill `circleFallback1 := R0P.SemSource.circleFallback1` in
`sourceData`, then update consumers and D2 after the lead recompiles R0C.

```diff
--- a/R0C/SemStatement.lean
+++ b/R0C/SemStatement.lean
@@ -44,6 +44,8 @@
 words may occur in SM, so later commitments are not moved before lambda/chi. -/
 structure SourceData (X SM W : Type) (Sfield : Fin 29 → Subfield E) where
   semanticRounds : Nat
+  /-- Reserved second-row fallback, supplied by the concrete source instance. -/
+  circleFallback1 : Point K
   semanticBad : Prefix K E X SM → SM → K → Prop
   paymentWitness : X → W → Prop
   openingView : Prefix K E X SM →
@@ -51,7 +53,7 @@
   decision : Prefix K E X SM → Msg K E SM → Bool
 
 /-- A challenge event, not a side condition on the initial statement. -/
-def z0Bad (z : Point K) : Prop := BaseRational z
+def z0Bad (fallback1 z : Point K) : Prop := BaseRational z ∨ z = fallback1
 
 def z1Bad (z0 z1 : Point K) : Prop := BaseRational z1 ∨ z1 = z0
 
@@ -77,7 +79,7 @@
     (P : Prefix K E X SM) (m : Msg K E SM) (c : Chal K E) : Prop :=
   (∃ sm k, P.round < s.semanticRounds ∧ m = .semantic sm ∧ c = .semantic k ∧
     s.semanticBad P sm k) ∨
-  (∃ y z, P.round = s.semanticRounds ∧ m = .beforeZ0 y ∧ c = .circle z ∧ z0Bad z) ∨
+  (∃ y z, P.round = s.semanticRounds ∧ m = .beforeZ0 y ∧ c = .circle z ∧ z0Bad s.circleFallback1 z) ∨
   (∃ y y0 z0 z1, P.round = s.semanticRounds + 1 ∧
     P.rounds.getLast? = some (.beforeZ0 y, .circle z0) ∧
     m = .beforeZ1 y0 ∧ c = .circle z1 ∧ z1Bad z0 z1) ∨
--- a/R0C/CircleRows.lean
+++ b/R0C/CircleRows.lean
@@ -55,12 +55,13 @@
 theorem baseRational_card : Fintype.card {z : Point K // BaseRational z} = 2^31 :=
   (Fintype.card_congr (rationalEquiv (K := K))).symm.trans card_C_eq
 
-/-- Exact first-row density under the uniform law on the full circle. -/
-theorem z0_density : mean (fun z : Point K => indicator (SemStatement.z0Bad z)) =
-    (2^31 : ℚ) / Fintype.card (Point K) := by
-  simp only [SemStatement.z0Bad]
-  rw [Counting.mean_indicator_card, baseRational_card]
-  simp only [Nat.cast_pow, Nat.cast_ofNat]
+/-- The first-row event also includes the reserved second-row fallback. -/
+theorem z0_density_le (fallback1 : Point K) :
+    mean (fun z : Point K => indicator (SemStatement.z0Bad fallback1 z)) ≤
+      (2^31+1 : ℚ) / Fintype.card (Point K) := by
+  letI : Nonempty (Point K) := ⟨fallback1⟩
+  have h := Counting.mean_or_eq_le (BaseRational (K := K)) fallback1
+  simpa only [SemStatement.z0Bad, baseRational_card, Nat.cast_pow, Nat.cast_ofNat] using h
 
 /-- Second-row upper bound, including equality with the preceding challenge. -/
 theorem z1_density_le (z0 : Point K) :
@@ -72,13 +73,13 @@
 
 omit [Fintype K] in
 /-- Absence of the two counted events supplies precisely the old Stmt fields. -/
-theorem chord_conditions (z0 z1 : Point K)
-    (h0 : ¬ SemStatement.z0Bad z0) (h1 : ¬ SemStatement.z1Bad z0 z1) :
+theorem chord_conditions (fallback1 z0 z1 : Point K)
+    (h0 : ¬ SemStatement.z0Bad fallback1 z0) (h1 : ¬ SemStatement.z1Bad z0 z1) :
     z0 ≠ z1 ∧ ¬ BaseRational z0 ∧ ¬ BaseRational z1 := by
-  exact ⟨fun h => h1 (Or.inr h.symm), h0, fun h => h1 (Or.inl h)⟩
+  exact ⟨fun h => h1 (Or.inr h.symm), fun h => h0 (Or.inl h), fun h => h1 (Or.inl h)⟩
 
 #print axioms baseRational_card
-#print axioms z0_density
+#print axioms z0_density_le
 #print axioms z1_density_le
 #print axioms chord_conditions
 end
```

G21 and G23 remain pending. No Freeze claim is made. For the later generic
maxErr helper, note that its fold includes 0: `maxErr_eq_of_le` also needs the
selected value to be nonnegative, or should first prove equality to
`max (e j) 0`. This is an internal generic-lemma issue; the concrete budgets'
nonnegativity should be proved inside the requested result, not added as a
new premise to combined_fiat_shamir_closed.

Snapshot revision before the obstruction commit: `437c018e58212e61be24702235ca150221f4e938`.
Final source bytes match the accepted host snapshots 2703/2709. No source
outside the semantic job directory was edited, and evidence remains uncommitted.

## Lead: G22 obstruction accepted; R0C interface applied (673, 675)

Codex's `CircleMassObstruction` (`56a8e2315`) is correct: `qm31Sample` is
the modulo reduction of a 256-byte block, so a single parameter's mass is
up to `(1+δQ)/P⁴`, not `1/P⁴`. The lead's G22 targets were mis-stated by
the `(1+δQ)` factor already carried by the semantic rows; the design is
unchanged. Corrected targets: `circleSample0_mass ≤ (1+δQ)/P⁴` and
`circleSample1_mass (hz0 : z0 ≠ circleFallback1) ≤ (1+δQ)/P⁴`, via
`qm31Sample_mass_slack` on the one-parameter fibres.

R0C interface applied (lead edits, Codex's proposed shape):
`SourceData.circleFallback1 : Point K`; `z0Bad fallback1 z := BaseRational z
∨ z = fallback1`; `roundBad` passes `s.circleFallback1`; circle
`rowBudget` rows `2/P⁴` (an upper bound for `(1+δQ)/P⁴`, kept free of the
job-directory `δQ`); `CircleRows.z0_density_le` replaces `z0_density`;
`chord_conditions` takes `fallback1`. Host: 673 `R0C/SemStatement`
exit 0, 3.10 s, 6,799,044 KiB; 674 failed on a stale `#print axioms
z0_density` line; 675 `R0C/CircleRows` exit 0, 3.27 s, 6,788,544 KiB;
standard axioms, no warnings. Dependent R0P modules must be recompiled
against 673/675 (Codex, continuing G22).

### G22 continuation: corrected fallback masses (2710–2717)

Recompiled unchanged prerequisites in import order against the lead’s R0C.SemStatement 673 and R0C.CircleRows 675. CircleSampler now exposes only the two nonrational fallback samplers; both corrected mass theorems follow from the one-parameter fibers and qm31Sample_mass_slack. Attempt 2716 exposed the two prime-name mismatch; 2717 adds the explicit rational prime equality and is green, with standard axioms only, no error, warning, or sorryAx. Deleted CircleMassObstruction.lean as requested after these bounds passed; its accepted modulo-bias finding remains recorded above. SemView needs no chord-condition edit: openingView already tests the same explicit three chord conditions and passed 2711 unchanged.

Host `dombarker@100.108.41.90`; pinned Lean 4.32.0 and existing cache, one Lean job at a time. The existing `run_g15_lake.sh` adapter retains run2’s reservation and scope limits and invokes `lake env lean`: MemoryHigh=5G, MemoryMax=7G, MemorySwapMax=0, 900 s timeout, reservation 24+7 or 26+7 GiB as recorded by each raw host log. No cap increase or dependency build. Raw host artifacts remain in `evidence/`; hash-verified local copies are at `/tmp/r0-g22-cont-20261009/evidence/`. Evidence files are excluded from commits.

| Attempt | Target | exit / time exit | Wall | Peak RSS KiB | Swaps | Axiom lines | Source SHA-256 |
|---:|---|---:|---:|---:|---:|---:|---|
| 2710 | `R0P/SemSource` | 0 / 0 | 0:02.86 | 6796108 | 0 | 1 | `e79ce46d3ce2dc99e65aa99c78581f5069c66eec3dba4dae0dce09ec86f7a024` |
| 2711 | `R0P/SemView` | 0 / 0 | 0:03.10 | 6816232 | 0 | 2 | `01868627189632007beaac02e9036d71d4f268dfe9c3f4d8b51ee9964de528e1` |
| 2712 | `R0P/SemDecision` | 0 / 0 | 0:03.06 | 6806904 | 0 | 2 | `cf8c98e1bf6d5da3a2e725efd3790c4efc7e75fc32b0c650c310d875bf1f8971` |
| 2713 | `R0P/SemD3` | 0 / 0 | 0:03.01 | 6811444 | 0 | 2 | `68cd2542aff4f20ead2f5855663cf3e743817725f2714cc3400a21b0f651c74b` |
| 2714 | `R0P/SemD2` | 0 / 0 | 0:04.07 | 6841668 | 0 | 5 | `ef7b48c25eefa272398f78472ecbcbc9f5221a8465ef2f414cf711ba79af99d9` |
| 2715 | `R0P/SemPad` | 0 / 0 | 0:03.60 | 6830748 | 0 | 24 | `2734705552a97a2ef29f0a4c6c4a36fda6e2f7653fe972c7152f9896c91f13c1` |
| 2716 | `R0P/CircleSampler` | 1 / 1 | 0:12.08 | 6794448 | 0 | 19 | `9cd01db0ffbe9ecbb9cc9cf728f62fad891cb0c02636d42ffc94d1a1ef87d7a2` |
| 2717 | `R0P/CircleSampler` | 0 / 0 | 0:12.09 | 6832504 | 0 | 20 | `ee0e9a4be9447d043fbcf19fa2ff583f04456dd62bd8c27d9fd622781accde1d` |

Source revision(s): `ab6bbce28a64f8d208c49097ea64713af711321f`, plus the recorded source snapshots. Failed-attempt audit output is not accepted proof evidence.

### G22 continuation: D3 and semantic dependency rebuild (2718–2724)

All unchanged semantic dependencies passed against the new R0C interface. SemD3Glue imports CircleSampler and sets the concrete sourceData.circleFallback1 to the checked second fallback. Generic source lemmas use sourceDataWithFallback with the fallback supplied as data; the concrete d3 obligation has no added premise. Attempt 2724 passes all 56 axiom lines with only standard axioms, no errors or warnings.

Host `dombarker@100.108.41.90`; pinned Lean 4.32.0 and existing cache, one Lean job at a time. The existing `run_g15_lake.sh` adapter retains run2’s reservation and scope limits and invokes `lake env lean`: MemoryHigh=5G, MemoryMax=7G, MemorySwapMax=0, 900 s timeout, reservation 24+7 or 26+7 GiB as recorded by each raw host log. No cap increase or dependency build. Raw host artifacts remain in `evidence/`; hash-verified local copies are at `/tmp/r0-g22-cont-20261009/evidence/`. Evidence files are excluded from commits.

| Attempt | Target | exit / time exit | Wall | Peak RSS KiB | Swaps | Axiom lines | Source SHA-256 |
|---:|---|---:|---:|---:|---:|---:|---|
| 2718 | `R0P/SemAccept` | 0 / 0 | 0:02.87 | 6812844 | 0 | 2 | `02a046a9703bf95c8f5fa3cb489084e0862379ae6f020a48f0a4374b542019b4` |
| 2719 | `R0P/SemHonest` | 0 / 0 | 0:03.62 | 6830820 | 0 | 14 | `63c890ceebfe82d2ef16e73aed51b4acac0e6bc0af8c5fb3b0d5eca05034234f` |
| 2720 | `R0P/SemDeg` | 0 / 0 | 0:09.84 | 6874348 | 0 | 47 | `ed059e7d1a94b7f3819398fb7f03762c743ab04d51d0ccd1ba795e8f5d96294e` |
| 2721 | `R0P/SemDegFamilies` | 0 / 0 | 0:13.19 | 7002012 | 0 | 44 | `60daa294e557252938f4d87fb9eb93df7aca5eff51795abf595c140a3b15c3e1` |
| 2722 | `R0P/SemVirtualDeg` | 0 / 0 | 0:03.17 | 6813124 | 0 | 3 | `c7660c31f4d9c72d6b8b654450ffb6d4e6dc180de99b158c84e79d4f4874f4ee` |
| 2723 | `R0P/MessageDescent` | 0 / 0 | 0:03.01 | 6748832 | 0 | 1 | `d3cb1623aeb04289250ed3f5bc2a9c532b62da2c5465933f2240fca47da856c3` |
| 2724 | `R0P/SemD3Glue` | 0 / 0 | 0:22.47 | 6942000 | 0 | 56 | `6e17304965d8d6771475e85b38796d044abe1f2a634f336efdbad4b2f310475d` |

Source revision(s): `b583f7b39a4e58fd3f652b58a94be101d7c6cf0c`, plus the recorded source snapshots. Failed-attempt audit output is not accepted proof evidence.

### G22 continuation: circle rows and full D2 (2725–2729)

Focused prefix snapshots passed first for the new no-hit helper (2725), row 24 (2727), and row 25 (2728), before the complete SemD2Glue assembly (2729). Attempt 2726 failed on the concrete z0Bad versus z0Bad′ indicator instance and positivity recursion; the replacement keeps z0Bad′ atomic and uses explicit div_nonneg, with no cap or recursion-limit increase. The row-25 mass premise is derived from doomed: split off the last transcript pair, and equality with circleFallback1 would create a row-24 hit. combinedD2Budget now uses (1+deltaQ)/P⁴ for rows 24–25, and the sigma clauses select circleSample0/1. No new obligation premise. Final 2729: standard axioms only, no errors or warnings; the checked full source matches its SHA below.

Host `dombarker@100.108.41.90`; pinned Lean 4.32.0 and existing cache, one Lean job at a time. The existing `run_g15_lake.sh` adapter retains run2’s reservation and scope limits and invokes `lake env lean`: MemoryHigh=5G, MemoryMax=7G, MemorySwapMax=0, 900 s timeout, reservation 24+7 or 26+7 GiB as recorded by each raw host log. No cap increase or dependency build. Raw host artifacts remain in `evidence/`; hash-verified local copies are at `/tmp/r0-g22-cont-20261009/evidence/`. Evidence files are excluded from commits.

| Attempt | Target | exit / time exit | Wall | Peak RSS KiB | Swaps | Axiom lines | Source SHA-256 |
|---:|---|---:|---:|---:|---:|---:|---|
| 2725 | `R0P/SemD2Glue` | 0 / 0 | 0:08.01 | 6864488 | 0 | 11 | `0fd5afb4f8582f008502cbdcd4e9494a909e35dffda81d1df95fc1eed3cdede0` |
| 2726 | `R0P/SemD2Glue` | 1 / 1 | 0:10.97 | 6838888 | 0 | 18 | `e558677c819817d0d1942225ae65c0b4a70f940ffadd6c26dc019d93b0a59e83` |
| 2727 | `R0P/SemD2Glue` | 0 / 0 | 0:11.03 | 6875168 | 0 | 18 | `72b737585faa8dbf8c4612501d5c5253d8310a060312023c2171a62be0da1d57` |
| 2728 | `R0P/SemD2Glue` | 0 / 0 | 0:13.26 | 6887608 | 0 | 22 | `2af5e4cecb7b941ce760835dcd49354f914c22b92669caddf6c41f98c6ec6c7a` |
| 2729 | `R0P/SemD2Glue` | 0 / 0 | 0:16.38 | 6902268 | 0 | 29 | `196a197121ee0e86f9f6407c2f6557d5a894a5b9b43072e63dd299393ba609c9` |

Source revision(s): `113ecd8851404cde8f84632b194496cc39ad4b27`, plus the recorded source snapshots. Failed-attempt audit output is not accepted proof evidence.

### G22 continuation: combined decoder density (2730–2732)

Recompiled unchanged SemCharP and SemDuplexDecoder against the new concrete source. SemDuplexDensity carries the updated circleSample0/1 sigma clauses and reuses the now-checked D2 bound. All three targets pass with standard axioms only, no errors or warnings.

Host `dombarker@100.108.41.90`; pinned Lean 4.32.0 and existing cache, one Lean job at a time. The existing `run_g15_lake.sh` adapter retains run2’s reservation and scope limits and invokes `lake env lean`: MemoryHigh=5G, MemoryMax=7G, MemorySwapMax=0, 900 s timeout, reservation 24+7 or 26+7 GiB as recorded by each raw host log. No cap increase or dependency build. Raw host artifacts remain in `evidence/`; hash-verified local copies are at `/tmp/r0-g22-cont-20261009/evidence/`. Evidence files are excluded from commits.

| Attempt | Target | exit / time exit | Wall | Peak RSS KiB | Swaps | Axiom lines | Source SHA-256 |
|---:|---|---:|---:|---:|---:|---:|---|
| 2730 | `R0P/SemCharP` | 0 / 0 | 0:02.95 | 6827908 | 0 | 2 | `e31f972835a430f019d8d05995add7923e65282cf71ba957f4534bcaad10aa42` |
| 2731 | `R0P/SemDuplexDecoder` | 0 / 0 | 0:04.59 | 6835232 | 0 | 3 | `cc8dc9b73d6f98a43ba8a41771e1cf356cac5ad3a7e87b062f031e4e0ba86236` |
| 2732 | `R0P/SemDuplexDensity` | 0 / 0 | 0:04.46 | 6847828 | 0 | 4 | `b5a853dd2e9deff895cf7aff3ef5c322c039928e4506a92f30b8cd3366138dac` |

Source revision(s): `ec9da0e3bf365df360dc9457343097cd76fd64e7`, plus the recorded source snapshots. Failed-attempt audit output is not accepted proof evidence.

### G22 complete: decoder and theorem43 instance (2733–2735)

Unchanged SemDuplexDecodes and SemBridge recompiled against their updated import closure. SemFiatShamir now carries the two fallback sampler identities through the theorem43 instance; no other theorem premise changed. All requested R0P dependency-chain recompiles against R0C 673/675 are green. All 2733–2735 axiom audits use standard axioms only and contain no errors or warnings. G22 is complete; next is G21 accounting.

Host `dombarker@100.108.41.90`; pinned Lean 4.32.0 and existing cache, one Lean job at a time. The existing `run_g15_lake.sh` adapter retains run2’s reservation and scope limits and invokes `lake env lean`: MemoryHigh=5G, MemoryMax=7G, MemorySwapMax=0, 900 s timeout, reservation 24+7 or 26+7 GiB as recorded by each raw host log. No cap increase or dependency build. Raw host artifacts remain in `evidence/`; hash-verified local copies are at `/tmp/r0-g22-cont-20261009/evidence/`. Evidence files are excluded from commits.

| Attempt | Target | exit / time exit | Wall | Peak RSS KiB | Swaps | Axiom lines | Source SHA-256 |
|---:|---|---:|---:|---:|---:|---:|---|
| 2733 | `R0P/SemDuplexDecodes` | 0 / 0 | 0:11.32 | 6901972 | 0 | 9 | `f885ebfe138c092810c4bb0bd39d4dc7567a4aa4f93148a944edb06c421aa7d6` |
| 2734 | `R0P/SemBridge` | 0 / 0 | 0:03.31 | 6812280 | 0 | 9 | `fe026af913107a06834976b53f2545644d8babad418872e758b4a332b10d2217` |
| 2735 | `R0P/SemFiatShamir` | 0 / 0 | 0:05.41 | 6839320 | 0 | 4 | `a9272da739c89b2aa4046cf8be1a7d3c3bc95c2f2edf2a52bdff4f56f1bcee72` |

Source revision(s): `19e6daaf4edadc243ddf93b68ea34bbb0a4957b8`, plus the recorded source snapshots. Failed-attempt audit output is not accepted proof evidence.

### G21 complete: combined maximum and closed bound (2800–2802)

SemMaxErr first checks the generic fold bound and attained-maximum lemma (2800), including the necessary bound on the zero seed. The semantic, circle, and opening inequalities then pass separately from the assembly (2801). The semantic coefficient bound is symbolic by the semRoundBudget branches; the numerical comparison 435200/P⁴ ≤ C(9557,22)/C(262144,22) reuses SlackBits.bad_query_count and SlackObstruction.query_count, whose proofs use only 22 descending factors. No Pascal recurrence, finite-field enumeration, decide/native_decide, or cap increase is used. Final 2802 proves combined_maxErr and combined_fiat_shamir_closed; the latter retains exactly the checked theorem43 instance premises. All three runs are green with standard axioms only, no errors or warnings. Closed bound: Pr[accepts ∧ extractFails] ≤ Qtot · (1+delta0) · C(9557,22)/C(262144,22) + κ(Qtot).

Host `dombarker@100.108.41.90`; pinned Lean 4.32.0 and existing cache, one Lean job at a time. The existing `run_g15_lake.sh` adapter retains run2’s reservation and scope limits and invokes `lake env lean`: MemoryHigh=5G, MemoryMax=7G, MemorySwapMax=0, 900 s timeout, reservation 24+7 or 26+7 GiB as recorded by each raw host log. No cap increase or dependency build. Raw host artifacts remain in `evidence/`; hash-verified local copies are at `/tmp/r0-g22-cont-20261009/evidence/`. Evidence files are excluded from commits.

| Attempt | Target | exit / time exit | Wall | Peak RSS KiB | Swaps | Axiom lines | Source SHA-256 |
|---:|---|---:|---:|---:|---:|---:|---|
| 2800 | `R0P/SemMaxErr` | 0 / 0 | 0:02.83 | 6826932 | 0 | 2 | `57f86cd6f47d965c3a8a5d8d9f99732f53fda1a37c7374812696c4b5202862f5` |
| 2801 | `R0P/SemMaxErr` | 0 / 0 | 0:03.29 | 6843504 | 0 | 9 | `31240710df3211d97e40df6beadc288f380114a49a75b4e5004699fc86cd78de` |
| 2802 | `R0P/SemMaxErr` | 0 / 0 | 0:04.91 | 6851348 | 0 | 12 | `c17943a39ffd541de55d5c0d7aed2c1f975a8b8352ffc57dfd3037777f9f3069` |

Source revision(s): `b0b89d6edebb77fa0e1a091791e4130e71376f0b`, plus the recorded source snapshots. Failed-attempt audit output is not accepted proof evidence.

## Freeze

G22, G21, and G23 are complete. The final manifest `R0P/SemAll` imports all 55 other current R0P modules. Its single host replay, attempt 2900, returned Lean/scope exit=0 and time exit=0, wall 2.62 s, peak RSS 6,795,512 KiB, swaps 0, with no errors or warnings. No second final-manifest replay was run. The eight requested audits all report exactly `[propext, Classical.choice, Quot.sound]`; no sorryAx or additional axiom.

Final bound, under the unchanged round-count, four source decoder identities, and distinct-first-read bound of the theorem43 instance:

`Pr[accepts ∧ extractFails] ≤ Qtot · (1+delta0) · C(9557,22)/C(262144,22) + κ(Qtot)`.

`git rev-parse HEAD` immediately before this Freeze commit: `a1b0d583a926c774cc724dc2f08f6cf09fe388cf`. The manifest is the new source in this commit; its exact SHA is in the table. All other source bytes are already committed at that revision.

Preflight matched every current local source SHA to an accepted exit=0 host attempt, checked equality with the current host source, checked that its cached object exists, and reviewed all 766 supporting axiom lines. All are standard axioms or no axioms. The one historical warning is Core attempt 600’s style suggestion “try simp instead of simpa”; it is unchanged and does not occur in the final manifest run. The obsolete CircleMassObstruction source was deleted locally and from the host source directory; its finding and raw evidence remain recorded.

Host `dombarker@100.108.41.90`, pinned workspace `/home/dombarker/project-offloads/aspis-fs-generic-20261006`, Lean 4.32.0 and compiled cache. Final command: `sh run_g15_lake.sh 2900 R0P/SemAll 7000 7` (invokes `lake env lean`). Reservation 24+7 GiB; MemoryHigh=5G, MemoryMax=7G, MemorySwapMax=0, timeout 900 s, one Lean job at a time. No cap increase or package/dependency build. Accepted attempts below include the unchanged independent modules’ prior focused runs and the updated R0C-import closure’s G22 recompiles.

| Module | Accepted attempt | exit | Wall | Peak RSS KiB | Swaps | Axiom lines | Source SHA-256 |
|---|---:|---:|---:|---:|---:|---:|---|
| `Asset` | 710 | 0 | 0:01.60 | 3323420 | 0 | 3 | `2c36ba0a589d2e982ca55716f5093e6c5da4152454f24de26c71f9ad9d9ef424` |
| `CircleSampler` | 2717 | 0 | 0:12.09 | 6832504 | 0 | 20 | `ee0e9a4be9447d043fbcf19fa2ff583f04456dd62bd8c27d9fd622781accde1d` |
| `Copy` | 1098 | 0 | 0:02.99 | 3365140 | 0 | 32 | `28a37fcfab1c2a6235e42932d44156c7952e6311958317ce843adb9737709d0f` |
| `CopyConstants` | 1001 | 0 | 0:01.96 | 3348732 | 0 | 0 | `cca9bdd0d2988693652d23010e068155abe0bc52fe36d030dbd8c163fe4f4f68` |
| `CopyInputLinks` | 1498 | 0 | 0:05.06 | 3414580 | 0 | 43 | `7575812a8719c53c74a7736037a0f109dc34420f69709e0cf41f0de96a84ff95` |
| `CopyRegistry` | 1198 | 0 | 0:07.84 | 3620576 | 0 | 34 | `42a78275bbe6dccebc1a7843e7260b2591c25ed5add271c79e1db99d4e820906` |
| `Core` | 600 | 0 | 0:01.49 | 3327872 | 0 | 0 | `eba6bb784803b5f00922724efc9997a8d5ab6bc55cd8c100bffd8a397dabe1f9` |
| `CoreExt` | 1700 | 0 | 0:01.43 | 3327464 | 0 | 1 | `7b0a6820f1f6d446943447509edd40babf84801eb1f06aeabd868ff033d41188` |
| `Digest` | 899 | 0 | 0:08.09 | 3381620 | 0 | 13 | `928d531c7ae80fdb2a3865bf3b2eac2d1dea84c2892c413f5c4a63709947d26b` |
| `EmptyRoots` | 803 | 0 | 0:01.48 | 3310664 | 0 | 0 | `648c9aaccf1691b634b2a91f46348ecb1e2d7382a982dcbddff1dcc786b77cbc` |
| `Extraction` | 1598 | 0 | 0:02.18 | 3351276 | 0 | 24 | `1b0f05c9252142fb659e2eaad2d528c42c9dbc405668e1e982d891ba424ca019` |
| `LaneMap` | 1799 | 0 | 0:09.38 | 3412060 | 0 | 44 | `122aa0b15111da62ae6672051c43a1cfe792e6cd240974669af87732539f6e17` |
| `LogUpAssembly` | 631 | 0 | 0:01.51 | 3340248 | 0 | 1 | `ccd2282e2da4669ed9f7c48d8260e38fda2361b8af3e69592e4ffcc38ce20a24` |
| `LogUpChain` | 1814 | 0 | 0:04.24 | 3386880 | 0 | 57 | `a9b0e52dd73026f356c16237d4b29527a70a479fc14cb0d59c178e1d94ff1fb6` |
| `LogUpCompress` | 1398 | 0 | 0:01.48 | 3323492 | 0 | 7 | `2a8ee84dbbc341e899441847ef68ed4f91c1a25d308a2124966bf3c587a32c4e` |
| `LogUpFrac` | 1298 | 0 | 0:01.20 | 2087160 | 0 | 8 | `f4d1c635188c74aeb5e2150e94b8627c22439e0bf1a482a173c0a5b38566b0b2` |
| `MessageDescent` | 2723 | 0 | 0:03.01 | 6748832 | 0 | 1 | `d3cb1623aeb04289250ed3f5bc2a9c532b62da2c5465933f2240fca47da856c3` |
| `Occupancy` | 712 | 0 | 0:01.79 | 3325912 | 0 | 2 | `2e12accc73c539ef79731f59f0a2b6ee760412afb90d5275c8ddedd36b77059d` |
| `Path` | 805 | 0 | 0:04.78 | 3340740 | 0 | 6 | `bb8ecd5b7b3880bd6cdf71ec06c6066195ce9a25b532111a21b861cc5833cb79` |
| `Poseidon` | 915 | 0 | 0:09.17 | 3423984 | 0 | 39 | `faeeefd8f3a6c25e1896eb827d9bd12d9bda901ff0171675186064baa5c369c8` |
| `PoseidonConstants` | 900 | 0 | 0:01.50 | 3310196 | 0 | 0 | `c87e94b63a575b96cecff98eea6a84385945d5481054a688d24ba162452340b0` |
| `Positive` | 713 | 0 | 0:01.57 | 3318348 | 0 | 3 | `7c318b973fcda478a003fb302d75eb75b6af318cca6d8e572ca66cd17dcfba3a` |
| `Positivity` | 602 | 0 | 0:01.80 | 3327496 | 0 | 1 | `0a7eaab784bc129b9995e3b7f18efde393e7d383686d1798bbe9fa7893a6ad1c` |
| `PositivityChain` | 608 | 0 | 0:01.38 | 3319404 | 0 | 3 | `480aaa1f5393862e55becb598566f85fe54ab6116f729ba11c1f5918440b481c` |
| `PositivityWired` | 604 | 0 | 0:01.79 | 3328412 | 0 | 1 | `9d601f1920c4700f2f08566cef66c9e43b5d3e9fceb9f9d9cc1ef4ce4471c7f2` |
| `Schedule` | 898 | 0 | 0:13.81 | 3433612 | 0 | 31 | `393e5edd57671f64647056130ea5b184a65dabb2b0069c45b1cf9afa1f058fb6` |
| `SemAccept` | 2718 | 0 | 0:02.87 | 6812844 | 0 | 2 | `02a046a9703bf95c8f5fa3cb489084e0862379ae6f020a48f0a4374b542019b4` |
| `SemAll` | 2900 | 0 | 0:02.62 | 6795512 | 0 | 8 | `6a7101dc97f8c720a07041d241ef43116c77a757a164332cfb07b16cdfee5f0d` |
| `SemAssembly` | 630 | 0 | 0:01.42 | 3328224 | 0 | 4 | `7ef49bd9a94338bc5b8aeda48fa08f415bdb57cf14bd483e4475ceff0b6c17fc` |
| `SemBadSets` | 1699 | 0 | 0:04.64 | 2162908 | 0 | 41 | `b74e1d7adfaaf6ad0c4973b96461b6359d23b62d6cadb6e2983646d3e5b40b5d` |
| `SemBridge` | 2734 | 0 | 0:03.31 | 6812280 | 0 | 9 | `fe026af913107a06834976b53f2545644d8babad418872e758b4a332b10d2217` |
| `SemCharP` | 2730 | 0 | 0:02.95 | 6827908 | 0 | 2 | `e31f972835a430f019d8d05995add7923e65282cf71ba957f4534bcaad10aa42` |
| `SemClosed` | 1815 | 0 | 0:01.42 | 3332880 | 0 | 2 | `05ed018167483ebe6cb14b4064d2dd7aa4a4ec8da950592bc88ee7ab4f30f7cf` |
| `SemD2` | 2714 | 0 | 0:04.07 | 6841668 | 0 | 5 | `ef7b48c25eefa272398f78472ecbcbc9f5221a8465ef2f414cf711ba79af99d9` |
| `SemD2Glue` | 2729 | 0 | 0:16.38 | 6902268 | 0 | 29 | `196a197121ee0e86f9f6407c2f6557d5a894a5b9b43072e63dd299393ba609c9` |
| `SemD3` | 2713 | 0 | 0:03.01 | 6811444 | 0 | 2 | `68cd2542aff4f20ead2f5855663cf3e743817725f2714cc3400a21b0f651c74b` |
| `SemD3Glue` | 2724 | 0 | 0:22.47 | 6942000 | 0 | 56 | `6e17304965d8d6771475e85b38796d044abe1f2a634f336efdbad4b2f310475d` |
| `SemDecision` | 2712 | 0 | 0:03.06 | 6806904 | 0 | 2 | `cf8c98e1bf6d5da3a2e725efd3790c4efc7e75fc32b0c650c310d875bf1f8971` |
| `SemDeg` | 2720 | 0 | 0:09.84 | 6874348 | 0 | 47 | `ed059e7d1a94b7f3819398fb7f03762c743ab04d51d0ccd1ba795e8f5d96294e` |
| `SemDegFamilies` | 2721 | 0 | 0:13.19 | 7002012 | 0 | 44 | `60daa294e557252938f4d87fb9eb93df7aca5eff51795abf595c140a3b15c3e1` |
| `SemDuplexDecoder` | 2731 | 0 | 0:04.59 | 6835232 | 0 | 3 | `cc8dc9b73d6f98a43ba8a41771e1cf356cac5ad3a7e87b062f031e4e0ba86236` |
| `SemDuplexDecodes` | 2733 | 0 | 0:11.32 | 6901972 | 0 | 9 | `f885ebfe138c092810c4bb0bd39d4dc7567a4aa4f93148a944edb06c421aa7d6` |
| `SemDuplexDensity` | 2732 | 0 | 0:04.46 | 6847828 | 0 | 4 | `b5a853dd2e9deff895cf7aff3ef5c322c039928e4506a92f30b8cd3366138dac` |
| `SemFiatShamir` | 2735 | 0 | 0:05.41 | 6839320 | 0 | 4 | `a9272da739c89b2aa4046cf8be1a7d3c3bc95c2f2edf2a52bdff4f56f1bcee72` |
| `SemHonest` | 2719 | 0 | 0:03.62 | 6830820 | 0 | 14 | `63c890ceebfe82d2ef16e73aed51b4acac0e6bc0af8c5fb3b0d5eca05034234f` |
| `SemLedger` | 622 | 0 | 0:01.56 | 3327488 | 0 | 4 | `12c257ec303dda29a2dd30b87b3c4f440e934ad1a5efd43cf9c26a29a2b0ad9b` |
| `SemMaxErr` | 2802 | 0 | 0:04.91 | 6851348 | 0 | 12 | `c17943a39ffd541de55d5c0d7aed2c1f975a8b8352ffc57dfd3037777f9f3069` |
| `SemPad` | 2715 | 0 | 0:03.60 | 6830748 | 0 | 24 | `2734705552a97a2ef29f0a4c6c4a36fda6e2f7653fe972c7152f9896c91f13c1` |
| `SemRounds` | 1999 | 0 | 0:04.02 | 3396240 | 0 | 55 | `564b9026233a36736f524407f357b44e173173139e52b9c4c6effbd88335bfd4` |
| `SemSource` | 2710 | 0 | 0:02.86 | 6796108 | 0 | 1 | `e79ce46d3ce2dc99e65aa99c78581f5069c66eec3dba4dae0dce09ec86f7a024` |
| `SemView` | 2711 | 0 | 0:03.10 | 6816232 | 0 | 2 | `01868627189632007beaac02e9036d71d4f268dfe9c3f4d8b51ee9964de528e1` |
| `SemVirtualDeg` | 2722 | 0 | 0:03.17 | 6813124 | 0 | 3 | `c7660c31f4d9c72d6b8b654450ffb6d4e6dc180de99b158c84e79d4f4874f4ee` |
| `Semantics` | 613 | 0 | 0:01.66 | 3341880 | 0 | 2 | `9309c5faa3de30d4f35bfe46509fe335a821d89a43051201a97232c0b89dc615` |
| `Sumcheck` | 628 | 0 | 0:00.91 | 1944708 | 0 | 1 | `c47147f826d471b479004d70328ea549c06d07f0b05d976f57bee3563d8c267d` |
| `Value` | 711 | 0 | 0:02.43 | 3339316 | 0 | 6 | `90afff5dd9c8b70c6c183f6b3f2322d85d57fbcb548b530a98f69a91f1bccc12` |
| `Zerocheck` | 629 | 0 | 0:01.35 | 1964756 | 0 | 3 | `ca1cbef230abd8829f89deb5638658a0b9c38b0c788fe3c34792e3bdc185a41b` |

Final manifest audit output:

```text
'R0P.SemDuplex.combined_fiat_shamir_closed' depends on axioms: [propext, Classical.choice, Quot.sound]
'R0P.SemSource.combinedProtocol_D2' depends on axioms: [propext, Classical.choice, Quot.sound]
'R0P.SemD3Glue.d3' depends on axioms: [propext, Classical.choice, Quot.sound]
'R0P.SemSource.virtualDeg' depends on axioms: [propext, Classical.choice, Quot.sound]
'R0P.SemSource.honestRows' depends on axioms: [propext, Classical.choice, Quot.sound]
'R0P.SemSource.checksAccept' depends on axioms: [propext, Classical.choice, Quot.sound]
'R0P.SemSource.circleSample0_mass' depends on axioms: [propext, Classical.choice, Quot.sound]
'R0P.SemSource.circleSample1_mass' depends on axioms: [propext, Classical.choice, Quot.sound]
```

Raw attempt logs, time reports, source snapshots, and SHA receipts remain uncommitted in host `evidence/`; this continuation’s verified copies are in `/tmp/r0-g22-cont-20261009/evidence/`. Source/hash and axiom preflight inventories are retained beside them. No Lean source outside the job directory was edited.

### G24: masked protocol foundation (3200–3201)

Base d2b7413259a75100db9d1c722d88932bfea28fb9, v8-reference. Fixed privacy LOG D3 (238–252) supplies the 32-row schedule: C2 is sent before theta at index 2, eta at 14, alpha at 15–24, circles at 25–26, opening at 27–31. New MaskProtocol extends only the inner semantic message type and keeps the R0C outer tags. Its parameterized sampler covers both schedules; combinedSamplerAt_31 proves exact equality with the frozen 31-row sampler. combinedProtocolZ has r=32 and retains the existing extraction function. The terminal and sumcheck checks use maskPoly + eta*original and the claim m′. MaskDegree is the atomic wrapper for the existing SemDegree.VDeg 10 (fun _ => 27): SemBadSets.VDeg does not exist in this base. virtualPolyZ_vdeg/indDeg use SemVirtualDeg.vdeg_virtualPoly (38–42), vdeg_smul, and vdeg_add. The frozen alpha degree was already 27 (SemD3:44–56, SemDecision:97–109, SemRounds:757–760), not 26. Totals reuse Zerocheck.bsumB (32–35,59–72), the same sum in SemRounds:790–795; SemD2 supplies candidate aggregation rather than a separate trace-sum function. Attempt 3200 lacked named dependent-if guards in schedule bounds; 3201 supplies them and passes with standard axioms only, no errors or warnings. The user explicitly corrected the eta sampler denominator to P⁴ during this run; ideal uniform SemE density still uses card SemE=P⁸. This checkpoint does not claim D2, D3Z, or a masked FS theorem. No frozen soundness source, R0C source, R0Z source, or Rust file was edited.

Host `dombarker@100.108.41.90`; pinned Lean 4.32.0 and existing cache, one Lean job at a time. The user-requested `sh run2.sh N Module 7000 7` invokes the pinned Lean executable with -j1 and asynchronous elaboration disabled: MemoryHigh=5G, MemoryMax=7G, MemorySwapMax=0, 900 s timeout, reservation 24+7 or 26+7 GiB as recorded by each raw host log. No cap increase or dependency build. Raw host artifacts remain in `evidence/`; hash-verified local copies are at `/tmp/r0-g24-20261009/evidence/`. Evidence files are excluded from commits.

| Attempt | Target | exit / time exit | Wall | Peak RSS KiB | Swaps | Axiom lines | Source SHA-256 |
|---:|---|---:|---:|---:|---:|---:|---|
| 3200 | `R0P/MaskProtocol` | 1 / 1 | 0:04.02 | 6805392 | 0 | 12 | `b49097e4f325a3c9664872726b822c89f11d342d2c5625d1ebfb0f39554f1478` |
| 3201 | `R0P/MaskProtocol` | 0 / 0 | 0:04.20 | 6841932 | 0 | 12 | `c00c51800d7895c38aa079d747e509e61137a3aaaeb500d656c5acd7d61796d0` |

Source revision(s): `d2b7413259a75100db9d1c722d88932bfea28fb9`, plus the recorded source snapshots. Failed-attempt audit output is not accepted proof evidence.

### Lead — G22 source change applied (circle fallback in the reference Rust)

`Transcript::challenge_reference_circle_point(sample)` (aspis-core transcript.rs)
replaces the retry loop for the R0 reference schedule: one `challenge_qm31`
parameter, the secure rational map, and on rejection the fixed row fallback
`CIRCLE_FALLBACK_PARAMETERS = [(0,1), (1,1)]` in `(c0,c1)` tower order, i.e.
`R0P.CircleSampler.circleFallbackParameter0/1`. Call sites switched: verifier
`state_only_prefix.rs` (both schedule paths), prover `state_only_proof.rs` and
`state_only_spend.rs`. The legacy `challenge_secure_circle_point` is retained
for callers outside the model. Tests: transcript unit tests (fallback points
accepted, distinct, outside CM31; one block per row on a CM31-only backend;
accepted draws identical to the legacy sampler) and release
`state_only_full_proof` rate16/rate32 round-trips pass. Refinement item: Rust
`challenge_qm31` is per-limb rejection (exactly uniform), whereas `qm31Sample`
models a one-block modulo law with slack δQ; the bridge is for the refinement
block.

### G24: eta one-root density and candidate aggregation (3202–3206)

MaskD2 proves etaBad_root, the generic atom-bound transfer, uniform density 1/card K, and the authorized semantic-sampler bound (1+deltaQ)/P⁴. None needs any property of maskPoly or hMask. The zero-slope branch is the empty event; the other branch is contained in the singleton {(m′−M)/S}. Generic finite counting stays symbolic. Attempt 3202 needed the FS namespace and an unused section-variable omission; 3203 found mean_const’s unnecessary Nonempty requirement, removed by proving the zero mean directly; 3204 passes the focused one-root part. Attempt 3205 needed an explicit field proof of 2≠1 in the aggregation diagnostic; 3206 passes all ten audits. The candidate-union lemmas establish cardinality ≤ number of candidates and the corresponding sampler bound. etaBad_two_roots proves, over any field with 2≠0, that claim 2 and mask sum 0 have distinct roots eta=2 for original sum 1 and eta=1 for original sum 2. This is a generic aggregation diagnostic, not a constructed counterexample inside the concrete Lambda list. SemD2:38–64 bounds that list by 100; :111–164 unions per-candidate events. Thus the one-root theorem alone does not justify a coefficient-1 global eta budget. The lead was asked whether the aggregate eta budget should carry the existing candidate factor 100; no new premise or silently weakened global D2 theorem is introduced. All green audits use only the standard three axioms. This module is the checked local density/aggregation checkpoint, not full FS2.D2.

Host `dombarker@100.108.41.90`; pinned Lean 4.32.0 and existing cache, one Lean job at a time. The user-requested `sh run2.sh N Module 7000 7` invokes the pinned Lean executable with -j1 and asynchronous elaboration disabled: MemoryHigh=5G, MemoryMax=7G, MemorySwapMax=0, 900 s timeout, reservation 24+7 or 26+7 GiB as recorded by each raw host log. No cap increase or dependency build. Raw host artifacts remain in `evidence/`; hash-verified local copies are at `/tmp/r0-g24-20261009/evidence/`. Evidence files are excluded from commits.

| Attempt | Target | exit / time exit | Wall | Peak RSS KiB | Swaps | Axiom lines | Source SHA-256 |
|---:|---|---:|---:|---:|---:|---:|---|
| 3202 | `R0P/MaskD2` | 1 / 1 | 0:02.88 | 6796580 | 0 | 7 | `34ee92114c4fe8cf26d1e75e7096a48982515be81d76c060ab41ddeb5d0b6a05` |
| 3203 | `R0P/MaskD2` | 1 / 1 | 0:03.02 | 6798508 | 0 | 7 | `687e5b84c68a13b15d82e8ec59e0e579ece80c170b7cbe005bf39f88396204ce` |
| 3204 | `R0P/MaskD2` | 0 / 0 | 0:03.05 | 6832960 | 0 | 7 | `4e7134d95b86afe0b8a130a711d5aabbcf6ea8930fe31ea1372bca3235782520` |
| 3205 | `R0P/MaskD2` | 1 / 1 | 0:03.26 | 6800572 | 0 | 10 | `00e7a2c6096081949430c79f109fbed443cb6a7cef545fa310ef935037b60ffd` |
| 3206 | `R0P/MaskD2` | 0 / 0 | 0:03.42 | 6833744 | 0 | 10 | `1adbf173b5ed4d92157f8ffe13e1d79d98cd8df370377848007b19780f064cba` |

Source revision(s): `8e879d8d4f3ab8dfee1e23d378609add64aa9719`, `91af84ab4a6b88f7274ea34e1b26354e5cb19035`, plus the recorded source snapshots. Failed-attempt audit output is not accepted proof evidence.

### G24: round-parameterized completing decoder (3207–3211)

MaskDuplexDecoder parameterizes the inner semantic message type and total round count, keeps the last eight-pair opening chain, and supplies combinedDecZ at 32. The chain law is proved by induction. combinedChainBS_31 and combinedDec_31 recover the frozen chain and decoder exactly; no frozen module was modified. Attempts 3207–3210 exposed match-elaboration and helper-unfolding differences in the reinstantiation proof. The final proof explicitly eliminates parse/decode/walk cases, rewrites their equations, and reuses the existing combinedAccFrom helper. Attempt 3211 is exit=0 with no errors or warnings and six standard-axiom audit lines. The opening-chain comparison is generic in the opening offset. This is independent of the pending global eta candidate budget.

Host `dombarker@100.108.41.90`; pinned Lean 4.32.0 and existing cache, one Lean job at a time. The user-requested `sh run2.sh N Module 7000 7` invokes the pinned Lean executable with -j1 and asynchronous elaboration disabled: MemoryHigh=5G, MemoryMax=7G, MemorySwapMax=0, 900 s timeout, reservation 24+7 or 26+7 GiB as recorded by each raw host log. No cap increase or dependency build. Raw host artifacts remain in `evidence/`; hash-verified local copies are at `/tmp/r0-g24-20261009/evidence/`. Evidence files are excluded from commits.

| Attempt | Target | exit / time exit | Wall | Peak RSS KiB | Swaps | Axiom lines | Source SHA-256 |
|---:|---|---:|---:|---:|---:|---:|---|
| 3207 | `R0P/MaskDuplexDecoder` | 1 / 1 | 0:04.72 | 6804684 | 0 | 6 | `36f144fec760015f852e37459368b3f4fbfa41b7bf120c4f7ab9961be943df4d` |
| 3208 | `R0P/MaskDuplexDecoder` | 1 / 1 | 0:04.85 | 6804488 | 0 | 6 | `8ffe4f935fa9d89a592684564a37e2ed86243d3fbc7a4caa4f984cb97c905e91` |
| 3209 | `R0P/MaskDuplexDecoder` | 1 / 1 | 0:04.85 | 6804196 | 0 | 6 | `34e98c68fd04bc88f6f28a11bd043cca2e30c3f862739fc22626e7fd6047107a` |
| 3210 | `R0P/MaskDuplexDecoder` | 1 / 1 | 0:04.89 | 6805420 | 0 | 6 | `6f3c59c367448f0abaaa26724027970a48b925e9c080da3fb866b7b1c5f40857` |
| 3211 | `R0P/MaskDuplexDecoder` | 0 / 0 | 0:04.91 | 6838708 | 0 | 6 | `17b1b947a0e15271565d9c956aabaeccd5a9d3ce58ad75f4b0b6b63fd7aafc6c` |

Source revision(s): `046dc1f2d2f7240865a10f72cc2832a2128c9640`, `365ca4808bf8383f0f4438e96685a3fe41166566`, plus the recorded source snapshots. Failed-attempt audit output is not accepted proof evidence.

### G24: generic protocol and chain-density transfer (3212–3213)

MaskDuplexDensity provides combinedProtocolAt for arbitrary inner messages and total rounds, with checked definitional reinstantiations of the frozen 31-round protocol and combinedProtocolZ at 32. combinedOwn_law treats a single-squeeze row or the final q22 chain. combinedChainDensity_of_D2 transfers any supplied FS2.D2 for any RoundByRound predicate; it does not assume the pending masked D2 obligation. Attempt 3212 lacked the import supplying the existing chainS_independentMean lemma; 3213 imports SemD2Glue and passes all four audits with standard axioms, no errors or warnings. The generic result has no hard-coded 31/32 count and makes no change to a frozen source.

Host `dombarker@100.108.41.90`; pinned Lean 4.32.0 and existing cache, one Lean job at a time. The user-requested `sh run2.sh N Module 7000 7` invokes the pinned Lean executable with -j1 and asynchronous elaboration disabled: MemoryHigh=5G, MemoryMax=7G, MemorySwapMax=0, 900 s timeout, reservation 24+7 or 26+7 GiB as recorded by each raw host log. No cap increase or dependency build. Raw host artifacts remain in `evidence/`; hash-verified local copies are at `/tmp/r0-g24-20261009/evidence/`. Evidence files are excluded from commits.

| Attempt | Target | exit / time exit | Wall | Peak RSS KiB | Swaps | Axiom lines | Source SHA-256 |
|---:|---|---:|---:|---:|---:|---:|---|
| 3212 | `R0P/MaskDuplexDensity` | 1 / 1 | 0:04.36 | 6810024 | 0 | 4 | `0681afbb7deb554c20e839b08d90bd09ad6b27d39780cd9fe6b4240811d42774` |
| 3213 | `R0P/MaskDuplexDensity` | 0 / 0 | 0:04.63 | 6847468 | 0 | 4 | `fd14411944ba5458d288ab93918a1d1a3619b43ee19d55d01a189c3c8f91eeab` |

Source revision(s): `5a4b88db392469689ce6c1eea09d47628d118b31`, plus the recorded source snapshots. Failed-attempt audit output is not accepted proof evidence.

### G24: generic chain and trace-order helpers (3214)

MaskDuplexChain ports the chain state, run output, cell-read, and traceFrom order lemmas with an arbitrary inner semantic message type. No schedule count occurs in these lemmas. Attempt 3214 passes seven audits, all within the standard three axioms, with no errors or warnings; it is the focused predecessor for generic decoding.

Host `dombarker@100.108.41.90`; pinned Lean 4.32.0 and existing cache, one Lean job at a time. The user-requested `sh run2.sh N Module 7000 7` invokes the pinned Lean executable with -j1 and asynchronous elaboration disabled: MemoryHigh=5G, MemoryMax=7G, MemorySwapMax=0, 900 s timeout, reservation 24+7 or 26+7 GiB as recorded by each raw host log. No cap increase or dependency build. Raw host artifacts remain in `evidence/`; hash-verified local copies are at `/tmp/r0-g24-20261009/evidence/`. Evidence files are excluded from commits.

| Attempt | Target | exit / time exit | Wall | Peak RSS KiB | Swaps | Axiom lines | Source SHA-256 |
|---:|---|---:|---:|---:|---:|---:|---|
| 3214 | `R0P/MaskDuplexChain` | 0 / 0 | 0:03.80 | 6842600 | 0 | 7 | `e4c2d092dda27b2b517a03ff2885dfd37789621c6ca489e726601ea5f5227956` |

Source revision(s): `045635fe67362b5a235f6cf9e821b71f0049d53b`, plus the recorded source snapshots. Failed-attempt audit output is not accepted proof evidence.

### G24: generic transcript and collision decoding (3215–3216)

MaskDuplexDecodes proves combinedDecodes for n+2 rounds and arbitrary inner semantic messages, using p.rounds=n+2. The former row-29/30 argument now uses predecessor n and final row n+1; all earlier rounds are single squeezes and the final row uses the eight-pair chain. Attempt 3215 required the symbolic identity n+2-1=n+1 in the branch reductions; 3216 uses this named arithmetic fact and passes all six audits with standard axioms, no errors or warnings. The proof does not depend on the mask polynomial, semantic bad sets, or eta budget. It supplies the decodes part of Inj3; the full masked D2/D3 and FS instance are not asserted here.

Host `dombarker@100.108.41.90`; pinned Lean 4.32.0 and existing cache, one Lean job at a time. The user-requested `sh run2.sh N Module 7000 7` invokes the pinned Lean executable with -j1 and asynchronous elaboration disabled: MemoryHigh=5G, MemoryMax=7G, MemorySwapMax=0, 900 s timeout, reservation 24+7 or 26+7 GiB as recorded by each raw host log. No cap increase or dependency build. Raw host artifacts remain in `evidence/`; hash-verified local copies are at `/tmp/r0-g24-20261009/evidence/`. Evidence files are excluded from commits.

| Attempt | Target | exit / time exit | Wall | Peak RSS KiB | Swaps | Axiom lines | Source SHA-256 |
|---:|---|---:|---:|---:|---:|---:|---|
| 3215 | `R0P/MaskDuplexDecodes` | 1 / 1 | 0:09.97 | 6870284 | 0 | 6 | `73f7bcf5865ecd6851cf6b7c9757d56dac2b6cdceb510f8beff583263273611a` |
| 3216 | `R0P/MaskDuplexDecodes` | 0 / 0 | 0:10.43 | 6917028 | 0 | 6 | `b542e082c2dc2a1f364aacd518b7523faab507d4a5ac6cd5aa5f97b2457555f2` |

Source revision(s): `530f93ad3857327171f17a4e56a4eca6d34a6b77`, plus the recorded source snapshots. Failed-attempt audit output is not accepted proof evidence.

### G24: accounting independent of the eta coefficient (3217)

MaskMaxErr inserts a parameter etaBudget at index 14 and shifts the remaining frozen rows. The frozen alpha budgets were already 27. combined_maxErrWithEta proves the exact 32-row maximum is epsilonSlack WideExact delta0 4 whenever etaBudget is at most that query row. combined_maxErrWithEta_coefficient supplies this comparison for every coefficient 0≤c≤217600 in (1+deltaQ)*c/P⁴, including 1 and 100, without choosing the global eta coefficient. It reuses the accepted symbolic numeric bound rather than expanding binomial recurrences. Consequently the closed maximum, conditional on the remaining semantic obligations and either proposed coefficient, is unchanged: (1+delta0)*C(9557,22)/C(262144,22), with counts 3204816658150512709790016143025871214703406297554365823658832464480 and 143459390671643080338858006328548634467103740668941284234642666778199466504034122047364474303283200. No new exponent is claimed. Attempt 3217 passes three standard-axiom audits with no errors or warnings. This generic accounting theorem is not combined_maxErrZ for a finalized masked D2 budget and is not a closed masked FS theorem.

Host `dombarker@100.108.41.90`; pinned Lean 4.32.0 and existing cache, one Lean job at a time. The user-requested `sh run2.sh N Module 7000 7` invokes the pinned Lean executable with -j1 and asynchronous elaboration disabled: MemoryHigh=5G, MemoryMax=7G, MemorySwapMax=0, 900 s timeout, reservation 24+7 or 26+7 GiB as recorded by each raw host log. No cap increase or dependency build. Raw host artifacts remain in `evidence/`; hash-verified local copies are at `/tmp/r0-g24-20261009/evidence/`. Evidence files are excluded from commits.

| Attempt | Target | exit / time exit | Wall | Peak RSS KiB | Swaps | Axiom lines | Source SHA-256 |
|---:|---|---:|---:|---:|---:|---:|---|
| 3217 | `R0P/MaskMaxErr` | 0 / 0 | 0:02.97 | 6833280 | 0 | 3 | `4377fc7c1b32616d4f53c20220b5e47dda2f940c22403c8073f1e6e6259fef35` |

Source revision(s): `63371a3d1909bec3ff4b16a2aea23568a3fe8d26`, plus the recorded source snapshots. Failed-attempt audit output is not accepted proof evidence.

### G24: Inj3 instances and theorem43 adapter (3218–3220)

MaskFiatShamir closes ChainsRead and ReadsChains for arbitrary inner semantic messages and n+2 rounds, builds the full generic Inj3, and re-instantiates it against the unchanged frozen protocol/decoder at 31 and the masked protocol/decoder at 32. The generic combined_fiat_shamir_of_obligations adapter proves theorem43 already exposes the needed round count; its D1/D2/D3 arguments are explicitly unclosed obligations, not premises added to a claimed combined_fiat_shamirZ. Attempt 3218 used theorem for the Type-valued Inj3 structure; 3219 changes these constructors to defs but needed numeral addition normalization at the two instances; 3220 passes all six audits with standard axioms and no errors or warnings. No frozen source or R0C source was edited.

Host `dombarker@100.108.41.90`; pinned Lean 4.32.0 and existing cache, one Lean job at a time. The user-requested `sh run2.sh N Module 7000 7` invokes the pinned Lean executable with -j1 and asynchronous elaboration disabled: MemoryHigh=5G, MemoryMax=7G, MemorySwapMax=0, 900 s timeout, reservation 24+7 or 26+7 GiB as recorded by each raw host log. No cap increase or dependency build. Raw host artifacts remain in `evidence/`; hash-verified local copies are at `/tmp/r0-g24-20261009/evidence/`. Evidence files are excluded from commits.

| Attempt | Target | exit / time exit | Wall | Peak RSS KiB | Swaps | Axiom lines | Source SHA-256 |
|---:|---|---:|---:|---:|---:|---:|---|
| 3218 | `R0P/MaskFiatShamir` | 1 / 1 | 0:04.55 | 6802664 | 0 | 3 | `6025e417edafa957dbdafe44d1feb62c2091c6205c00b879864fe0a0c3044b53` |
| 3219 | `R0P/MaskFiatShamir` | 1 / 1 | 0:04.57 | 6807652 | 0 | 6 | `f2059af30cb04f24044496819124f5e1472f99e51c44d134e57cfa2a00b7115b` |
| 3220 | `R0P/MaskFiatShamir` | 0 / 0 | 0:04.97 | 6841980 | 0 | 6 | `b119bbaa399868764c079869d639585af68050fe1ab3cbaa5181841e5475e438` |

Source revision(s): `a76fa643a87c119a3ad7d913ac3eb6267a3030b5`, plus the recorded source snapshots. Failed-attempt audit output is not accepted proof evidence.

### G24 stop: the global eta-row coefficient is unresolved

The user confirmed P⁴ for the actual sampler denominator. The checked
fixed-trace etaBad_semChal_mass is (1+deltaQ)/P⁴ and needs no assumption
about maskPoly. The independent generic decoder, density transfer, decoding,
Inj3 instances, theorem43 adapter, and parameterized maximum accounting are
now green and committed module by module. Every accepted local source was
rehashed against its host receipt (3201, 3206, 3211, 3213, 3214, 3216, 3217,
3220). The changed R0P files are exclusively new Mask* files. The frozen
31-round sources are byte-for-byte unchanged from base d2b741325; the generic
protocol/decoder equalities and Inj3 reinstantiation check their reuse.
No unchanged frozen-manifest replay was launched. No evidence file is staged.

The remaining fixed-budget assembly target, written in normalized notation
rather than presented as an emitted Lean error, is:

```lean
-- x : TypedContext SemE Sfield
-- rounds : List (Msg SemE SemE (SemMsg SemE) × Chal SemE SemE)
-- pre : Fin 14 → SemE; claim : SemE
-- maskPoly : (Fin 10 → SemE) → SemE
-- ts := candidates x rounds .none
-- total := fun t => originalTotal x.pub B t pre
-- M := maskTotal maskPoly
⊢ mean (fun s : State =>
    indicator (etaSomeBad ts total claim M (semChal s))) ≤
    (1 + deltaQ) / (AspisCircleGroupOrder.P : ℚ)^4
```

SemD2.candidates_card supplies ts.card≤100. The proved
etaSomeBad_semChal_mass supplies ts.card*(1+deltaQ)/P⁴; therefore the available
aggregate bound is 100*(1+deltaQ)/P⁴. A coefficient-1 bound for the concrete
candidate union, possibly exploiting the existing doomed-prefix conditions,
has not been proved. The generic two-root diagnostic is not a concrete
counterexample for Lambda. No trace-sum invariance or candidate uniqueness
premise has been introduced.

The fixed privacy LOG D3 budget is coefficient 1. The lead was asked whether
to use the candidate factor 100 or stop at this aggregation gap; that separate
question remains unanswered. Dependent global budget and semantic assembly
are stopped. There is no claimed combinedD2BudgetZ, complete FS2.D2 for the
masked protocol, MaskD3Glue/d3Z, combined_fiat_shamirZ, or combined_maxErrZ.
The explicit-obligation adapter and the coefficient-parameterized accounting
are auxiliary results only. Either proposed eta coefficient preserves the
query-row maximum by attempt 3217. No host Lean job remains from this worker.

### G24 continuation: authorized eta union and 32-row budget (3221–3222)

Fetched base 2363f469444bd383a352d5a5f43016cc98e2044d on v8-reference. The lead authorizes eta coefficient 100. etaCandidates_semChal_mass applies etaSomeBad_semChal_mass directly with SemD2.candidates_card, without uniqueness or trace-sum hypotheses. combinedD2BudgetZ is now fixed: rows 0–13 retain their frozen budgets; row 14 is 100*(1+deltaQ)/P⁴; alpha rows 15–24 are 2700*(1+deltaQ)/P⁴ (100 candidates times degree 27); circle rows 25–26 use the explicitly requested 2/P⁴ envelope; opening rows 27–31 retain the five existing epsilonSlack rows. The frozen alpha bound is already 27, despite the prompt referring to 26; frozen circle budgets are (1+deltaQ)/P⁴, below the new envelope. Attempt 3221 needed the delta0 namespace; 3222 passes all twelve audits with standard axioms and no errors or warnings. This replaces the prior budget-choice stop; full masked D2/D3 assembly is in progress.

Host `dombarker@100.108.41.90`; pinned Lean 4.32.0 and existing cache, one Lean job at a time. The user-requested `sh run2.sh N Module 7000 7` invokes the pinned Lean executable with -j1 and asynchronous elaboration disabled: MemoryHigh=5G, MemoryMax=7G, MemorySwapMax=0, 900 s timeout, reservation 24+7 or 26+7 GiB as recorded by each raw host log. No cap increase or dependency build. Raw host artifacts remain in `evidence/`; hash-verified local copies are at `/tmp/r0-g24-20261009/evidence/`. Evidence files are excluded from commits.

| Attempt | Target | exit / time exit | Wall | Peak RSS KiB | Swaps | Axiom lines | Source SHA-256 |
|---:|---|---:|---:|---:|---:|---:|---|
| 3221 | `R0P/MaskD2` | 1 / 1 | 0:03.58 | 6806772 | 0 | 12 | `8ef11e92cad973a46bead623620c042da986258c2655d3b635ad6dda3f00f2b4` |
| 3222 | `R0P/MaskD2` | 0 / 0 | 0:03.84 | 6840780 | 0 | 12 | `fa86046d9800c581b22bd068c64b8a9fbe98a2049cc20e05dc38c66bd3a03b8a` |

Source revision(s): `2363f469444bd383a352d5a5f43016cc98e2044d`, plus the recorded source snapshots. Failed-attempt audit output is not accepted proof evidence.

### G24 continuation: masked semantic core (3223)

MaskSemantics proves honestRowsZ with literal mask values at Boolean rows, checksAcceptZ for the masked target, and originalTotal_zero_of_masked_accept. The latter applies the existing virtualPolyZ_indDeg from hMask, Sumcheck.sound, virtualPolyZ_total, and the eta exclusion; it handles eta=0 without dividing by eta or adding a mask premise. semantic_of_total_zero reuses the downstream zerocheck, lane and LogUp arguments of SemD3.d3_core/SemClosed after replacing the original sumcheck step by the recovered zero sum. All four audits pass at 3223 with standard axioms, no errors or warnings. Prefix parsing and no-hit transport still have to discharge these local semantic hypotheses in masked D3.

Host `dombarker@100.108.41.90`; pinned Lean 4.32.0 and existing cache, one Lean job at a time. The user-requested `sh run2.sh N Module 7000 7` invokes the pinned Lean executable with -j1 and asynchronous elaboration disabled: MemoryHigh=5G, MemoryMax=7G, MemorySwapMax=0, 900 s timeout, reservation 24+7 or 26+7 GiB as recorded by each raw host log. No cap increase or dependency build. Raw host artifacts remain in `evidence/`; hash-verified local copies are at `/tmp/r0-g24-20261009/evidence/`. Evidence files are excluded from commits.

| Attempt | Target | exit / time exit | Wall | Peak RSS KiB | Swaps | Axiom lines | Source SHA-256 |
|---:|---|---:|---:|---:|---:|---:|---|
| 3223 | `R0P/MaskSemantics` | 0 / 0 | 0:03.11 | 6835164 | 0 | 4 | `e0159b7d5cbfa65b1b784d794f16673ca01b5384e82dc7841011091a7c8a078c` |

Source revision(s): `2abe95fa7ffd51ff0f390400c433618438c92ceb`, plus the recorded source snapshots. Failed-attempt audit output is not accepted proof evidence.

### G24 continuation: masked transcript and opening parsers (3224–3225)

MaskView parses 25 semantic rows, the maskSum claim at index 14, alpha polynomials at indices 15–24, two circle rows, and the existing five-row opening suffix. openingViewZ reuses openingStmt and its unchanged points/claims, with alpha read at the shifted indices. Parser structure/take lemmas and opening-good-to-hitFrom transport are proved with the semantic round count 25. decisionZ checks the parsed scalar claim and masked sumcheck target; it does not add an eta polynomial degree check. Attempt 3224 needed an explicit option-pattern type, a missing Sfield binder, SourceData field-name preservation, and folding the mapped-list induction hypothesis; 3225 passes nineteen standard-axiom audits with no errors or warnings. No frozen parser was modified.

Host `dombarker@100.108.41.90`; pinned Lean 4.32.0 and existing cache, one Lean job at a time. The user-requested `sh run2.sh N Module 7000 7` invokes the pinned Lean executable with -j1 and asynchronous elaboration disabled: MemoryHigh=5G, MemoryMax=7G, MemorySwapMax=0, 900 s timeout, reservation 24+7 or 26+7 GiB as recorded by each raw host log. No cap increase or dependency build. Raw host artifacts remain in `evidence/`; hash-verified local copies are at `/tmp/r0-g24-20261009/evidence/`. Evidence files are excluded from commits.

| Attempt | Target | exit / time exit | Wall | Peak RSS KiB | Swaps | Axiom lines | Source SHA-256 |
|---:|---|---:|---:|---:|---:|---:|---|
| 3224 | `R0P/MaskView` | 1 / 1 | 0:03.99 | 6812032 | 0 | 15 | `25f8f8878bea3a65c3c95c9ad6d3154ff9140496a2dc2f6acfe3bc76c03e35ea` |
| 3225 | `R0P/MaskView` | 0 / 0 | 0:04.61 | 6872088 | 0 | 19 | `17dc48a803d28ec18bc3c6c5f0dfeee5ee0207d8f69cdb3207dcdfb65e643b11` |

Source revision(s): `2d4ff9bab76ba7b6514570b38ebe1349d8fd4434`, plus the recorded source snapshots. Failed-attempt audit output is not accepted proof evidence.

### G24 continuation: shifted semantic classifier and alpha counts (3226)

MaskBadSets defines semanticBadZ with the exact guard 15≤P.rounds.length → degreeOK (unmaskSem sm). Within the semantic schedule the guard is active precisely on rows 15–24, the ten alpha rows whose current polynomial is degree-checked by the verifier. It is vacuous on rows 0–14. Row 14 instead requires a parsed .maskSum claim and uses etaSomeBad over the committed-word candidates; no verifier polynomial degree check suppresses this eta event. Earlier rows reuse semanticBad through the inner-message projection; alpha rows use the masked virtual polynomial, the already sampled eta, and alphaSomeBad. The degree-27 alpha root count is multiplied by candidate cardinality symbolically and transferred through semChal. Every predicate used at a concrete filter is def-wrapped. Attempt 3226 passes four standard-axiom audits without errors or warnings.

Host `dombarker@100.108.41.90`; pinned Lean 4.32.0 and existing cache, one Lean job at a time. The user-requested `sh run2.sh N Module 7000 7` invokes the pinned Lean executable with -j1 and asynchronous elaboration disabled: MemoryHigh=5G, MemoryMax=7G, MemorySwapMax=0, 900 s timeout, reservation 24+7 or 26+7 GiB as recorded by each raw host log. No cap increase or dependency build. Raw host artifacts remain in `evidence/`; hash-verified local copies are at `/tmp/r0-g24-20261009/evidence/`. Evidence files are excluded from commits.

| Attempt | Target | exit / time exit | Wall | Peak RSS KiB | Swaps | Axiom lines | Source SHA-256 |
|---:|---|---:|---:|---:|---:|---:|---|
| 3226 | `R0P/MaskBadSets` | 0 / 0 | 0:03.40 | 6839732 | 0 | 4 | `cbe7c19b7d3e153f5ff782795181b709015bb9f316d56159b8701e7f650780cb` |

Source revision(s): `1098cee2cb58d8d3c78842f8accb48b1ae5c0d80`, plus the recorded source snapshots. Failed-attempt audit output is not accepted proof evidence.

### G24 continuation: fixed masked maximum (3227–3228)

combined_maxErrZ now proves maxErr combinedD2BudgetZ 32 = epsilonSlack WideExact delta0 4 for the finalized budget. Row 14 contributes 100*(1+deltaQ)/P⁴; each alpha row 15–24 contributes 2700*(1+deltaQ)/P⁴ (27*100); circle rows 25–26 contribute 2/P⁴. The final q22 row 31 remains the attained maximum, exactly (1+delta0)*C(9557,22)/C(262144,22), with the same checked numerator and denominator as the frozen accounting. No changed exponent is introduced: the frozen alpha degree was already 27. Attempt 3227 was exit=0 with a sequencing-style warning; 3228 removes that warning and passes six standard-axiom audits. Full combined_fiat_shamirZ remains pending the D2/D3 assembly.

Host `dombarker@100.108.41.90`; pinned Lean 4.32.0 and existing cache, one Lean job at a time. The user-requested `sh run2.sh N Module 7000 7` invokes the pinned Lean executable with -j1 and asynchronous elaboration disabled: MemoryHigh=5G, MemoryMax=7G, MemorySwapMax=0, 900 s timeout, reservation 24+7 or 26+7 GiB as recorded by each raw host log. No cap increase or dependency build. Raw host artifacts remain in `evidence/`; hash-verified local copies are at `/tmp/r0-g24-20261009/evidence/`. Evidence files are excluded from commits.

| Attempt | Target | exit / time exit | Wall | Peak RSS KiB | Swaps | Axiom lines | Source SHA-256 |
|---:|---|---:|---:|---:|---:|---:|---|
| 3227 | `R0P/MaskMaxErr` | 0 / 0 | 0:03.14 | 6848668 | 0 | 6 | `d9082eec36a162329edc7d143f6bac224d5c748803d92b080af8f5e69efa9ac4` |
| 3228 | `R0P/MaskMaxErr` | 0 / 0 | 0:03.28 | 6845092 | 0 | 6 | `0f07ce9581f079a56d57c2e07acfdcccc824d3e4706d63951556673797fd9264` |

Source revision(s): `1b49bf79be2f11b5254d96270b591872ee4c5a5e`, plus the recorded source snapshots. Failed-attempt audit output is not accepted proof evidence.

### G24 continuation: all semantic sampler densities (3229–3230)

semantic_round_densityZ proves the authorized combinedD2BudgetZ bound for every semantic prefix below 25. Rows 0–13 transfer the frozen semantic density through baseRoundsZ; eta applies etaCandidates_semChal_mass directly; alpha applies the degree-27 candidate union bound and candidates_card. Failed degree checks and failed parsers produce empty classifier events. Attempt 3229 needed the mapped-prefix length and frozen budget normalized before transitivity in the early branch; 3230 passes its standard-axiom audit with no errors or warnings. No hMask or other polynomial fact is needed by root counting; hMask remains for masked sumcheck soundness.

Host `dombarker@100.108.41.90`; pinned Lean 4.32.0 and existing cache, one Lean job at a time. The user-requested `sh run2.sh N Module 7000 7` invokes the pinned Lean executable with -j1 and asynchronous elaboration disabled: MemoryHigh=5G, MemoryMax=7G, MemorySwapMax=0, 900 s timeout, reservation 24+7 or 26+7 GiB as recorded by each raw host log. No cap increase or dependency build. Raw host artifacts remain in `evidence/`; hash-verified local copies are at `/tmp/r0-g24-20261009/evidence/`. Evidence files are excluded from commits.

| Attempt | Target | exit / time exit | Wall | Peak RSS KiB | Swaps | Axiom lines | Source SHA-256 |
|---:|---|---:|---:|---:|---:|---:|---|
| 3229 | `R0P/MaskDensity` | 1 / 1 | 0:06.88 | 6820636 | 0 | 1 | `4ebb9305fd7bc079ba98d0e60ae877875cd13eb4b13c08da023429f8e02a1658` |
| 3230 | `R0P/MaskDensity` | 0 / 0 | 0:04.66 | 6855604 | 0 | 1 | `4431e71d58235625a8bc758c689e0c715c2b05d6e4b7975acb144b0c04893a5c` |

Source revision(s): `8f4194458620d41dd89bbd03c6fcf9dec28d6739`, plus the recorded source snapshots. Failed-attempt audit output is not accepted proof evidence.

### G24: masked source and definitional D1

MaskSource supplies the masked SourceData, the definitional D1 instance, the no-hit row bridge, and the explicit duplex-state witness for the opening challenge at row 27. Attempt 3231 exposed a predicate-wrapper rewrite mismatch; 3232 fixes it by making the paymentWitness proposition explicit. The accepted audit has only the standard axioms.

Host `dombarker@100.108.41.90`; pinned Lean 4.32.0 and existing cache, one Lean job at a time. The user-requested `sh run2.sh N Module 7000 7` invokes the pinned Lean executable with -j1 and asynchronous elaboration disabled: MemoryHigh=5G, MemoryMax=7G, MemorySwapMax=0, 900 s timeout, reservation 24+7 or 26+7 GiB as recorded by each raw host log. No cap increase or dependency build. Raw host artifacts remain in `evidence/`; hash-verified local copies are at `/tmp/r0-g24-20261009/evidence/`. Evidence files are excluded from commits.

| Attempt | Target | exit / time exit | Wall | Peak RSS KiB | Swaps | Axiom lines | Source SHA-256 |
|---:|---|---:|---:|---:|---:|---:|---|
| 3231 | `R0P/MaskSource` | 1 / 1 | 0:04.58 | 6805752 | 0 | 6 | `17f857cad5d88c220777227314d9ca47432ff82692a0e563e913afb466ece4c6` |
| 3232 | `R0P/MaskSource` | 0 / 0 | 0:04.71 | 6841572 | 0 | 6 | `511dcd8fbe119ba242aa2be3fadd501f479155e719516bcef409ce7b2427b3ac` |

Source revision(s): `d4070150ea84f2c410f69467468398a3037e048c`, plus the recorded source snapshots. Failed-attempt audit output is not accepted proof evidence.

### G24: semantic and circle D2 sub-bounds

MaskD2Glue proves the doomed-prefix flip containment and the semantic rows 0–24, circle row 25, and circle row 26 separately. Row 26 obtains z0 ≠ fallback1 from the absence of the row-25 hit. The sampler bounds (1+deltaQ)/P^4 are enlarged to the authorized 2/P^4 circle envelope. Attempts 3233–3234 exposed concrete field elaboration and wrapper mismatches; explicit WideExact types, sampler names and predicates resolve them without raising any limit. Attempt 3235 passes with the standard three axioms.

Host `dombarker@100.108.41.90`; pinned Lean 4.32.0 and existing cache, one Lean job at a time. The user-requested `sh run2.sh N Module 7000 7` invokes the pinned Lean executable with -j1 and asynchronous elaboration disabled: MemoryHigh=5G, MemoryMax=7G, MemorySwapMax=0, 900 s timeout, reservation 24+7 or 26+7 GiB as recorded by each raw host log. No cap increase or dependency build. Raw host artifacts remain in `evidence/`; hash-verified local copies are at `/tmp/r0-g24-20261009/evidence/`. Evidence files are excluded from commits.

| Attempt | Target | exit / time exit | Wall | Peak RSS KiB | Swaps | Axiom lines | Source SHA-256 |
|---:|---|---:|---:|---:|---:|---:|---|
| 3233 | `R0P/MaskD2Glue` | 1 / 1 | 0:50.26 | 6824656 | 0 | 4 | `d5e2eb565832d94209bb0ffee759340f642095bb45eac255789883a7a56d266d` |
| 3234 | `R0P/MaskD2Glue` | 1 / 1 | 0:50.12 | 6822188 | 0 | 4 | `7f242c89bcaec8d2487352108203090beac8214e1041b709228902118f8f7c68` |
| 3235 | `R0P/MaskD2Glue` | 0 / 0 | 0:08.28 | 6863968 | 0 | 5 | `b7ca10cd73187792cd8461ab6e5cb73403ddf84118ab630e679fb65b53e77dc7` |

Source revision(s): `ba8572b564459a7bb67f06d8a6b5b893c82ff740`, plus the recorded source snapshots. Failed-attempt audit output is not accepted proof evidence.

### G24: four shifted opening field rows

MaskOpeningDensity proves the all-message field opening bounds at rows 27–30. The roundBad opening disjunct identifies the local opening row; malformed messages or absent views have no flip event. Each uses the existing DQ.round_field_bound at local index 0–3. Attempt 3236 is green.

Host `dombarker@100.108.41.90`; pinned Lean 4.32.0 and existing cache, one Lean job at a time. The user-requested `sh run2.sh N Module 7000 7` invokes the pinned Lean executable with -j1 and asynchronous elaboration disabled: MemoryHigh=5G, MemoryMax=7G, MemorySwapMax=0, 900 s timeout, reservation 24+7 or 26+7 GiB as recorded by each raw host log. No cap increase or dependency build. Raw host artifacts remain in `evidence/`; hash-verified local copies are at `/tmp/r0-g24-20261009/evidence/`. Evidence files are excluded from commits.

| Attempt | Target | exit / time exit | Wall | Peak RSS KiB | Swaps | Axiom lines | Source SHA-256 |
|---:|---|---:|---:|---:|---:|---:|---|
| 3236 | `R0P/MaskOpeningDensity` | 0 / 0 | 0:04.23 | 6835876 | 0 | 2 | `e1b9fec9b1f1aae352ad5c75f00268ce917dcd0aea8111c5f19b1c8b189201ef` |

Source revision(s): `92e16f14288ae22b7a187c5176f9b40b7098c068`, plus the recorded source snapshots. Failed-attempt audit output is not accepted proof evidence.

### G24: shifted final q22 opening row

MaskOpeningDensity now includes the all-message final q22 bound at row 31. It averages DQ.round_q22_bound over the absorbed state via chainS_independentMean; no new sigma hypothesis is introduced. Malformed opening views have zero flip mass. Attempt 3237 used an unavailable indicator lemma; 3238 uses the existing indicator_iff API and is green.

Host `dombarker@100.108.41.90`; pinned Lean 4.32.0 and existing cache, one Lean job at a time. The user-requested `sh run2.sh N Module 7000 7` invokes the pinned Lean executable with -j1 and asynchronous elaboration disabled: MemoryHigh=5G, MemoryMax=7G, MemorySwapMax=0, 900 s timeout, reservation 24+7 or 26+7 GiB as recorded by each raw host log. No cap increase or dependency build. Raw host artifacts remain in `evidence/`; hash-verified local copies are at `/tmp/r0-g24-20261009/evidence/`. Evidence files are excluded from commits.

| Attempt | Target | exit / time exit | Wall | Peak RSS KiB | Swaps | Axiom lines | Source SHA-256 |
|---:|---|---:|---:|---:|---:|---:|---|
| 3237 | `R0P/MaskOpeningDensity` | 1 / 1 | 0:05.00 | 6804908 | 0 | 3 | `80dc39b3a0320db8cf19cde6b69c52b58d3c10e8632c2376973f4f11cd0138b2` |
| 3238 | `R0P/MaskOpeningDensity` | 0 / 0 | 0:05.22 | 6843520 | 0 | 3 | `efafabc1129c354576f83da5fde493395c063ce42efe54ff81c79b0ec3a0d6be` |

Source revision(s): `48a7e8bfe4a948d5fef06c91cd72aade2b9c0f28`, plus the recorded source snapshots. Failed-attempt audit output is not accepted proof evidence.
