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
