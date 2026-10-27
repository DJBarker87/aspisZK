# Decision: adopt the installation-specialised headline FJv_Deployed? (lead, 2026-10-27)

Status: DECISION REQUESTED from the owner. Nothing adopted.

## The two theorems

- `AspisR1.FJv_Top.deployed` (current proved top; strengthening of the
  adopted ARX_Root.deployed): quantifies over an arbitrary installation
  configuration `c : DrvC_Installation.Configuration`. Actual 83T/3P/13G.
  The three P rows: native L146 and F3Y_G_L146 (last semantic evaluation =
  exact masked spend terminal) and L154 (issued-query budget).
- `AspisR1.FJv_Deployed.deployed` (proved, standard axioms): FJv_Top
  instantiated at `IDa_Deployed.deployedConfiguration missing indexError
  reservation`, with native L146 and F3Y_G_L146 removed. Actual
  83T/1P/13G; the only P row is L154.

## Why L146 needs the specialisation

In the adopted statement the terminal is `c.boundaries.terminal`, a free
callback. `FJn_InstallationSeparation.not_uniform` proves that no uniform
identity with the installed terminal holds for arbitrary c (two different
constant terminals). A theorem quantified over every terminal must assume
L146. The deployed system uses one terminal, the extracted
`FIq_Terminal.terminal`; at that terminal, L146 is a proved fact
(FJt_/FJv_), not an assumption.

## What changes and what does not

Changes: the configuration binder `c` is replaced by the installed
configuration: finish (FIo_Install finish operations, including the fixed
pair FIo_Install.pair), boundaries (terminal := FIq_Terminal.terminal) and
std. Six inputs stay universally quantified with no condition: adapter,
currentBase, stageBase, reserved, query, geometry (query and geometry have
installed dictionaries, IDb_; reserved is an allocation outcome; the others
are emission adapters bound by the extraction premises). The L146 proof
uses none of them.

Unchanged: the adversary (arbitrary, adaptive), the two-transaction game,
RuntimePersistence, the admitted runtime, the extraction/trust premises,
the carriers, the collision event, every constant (Q+34, Q+1161, Q+2322,
Q+2965), the bound F3T_Numeric.total, its range, the exact zero-query
margin and the conclusion.

Nature: universal elimination on the implementation configuration, i.e. a
specialisation to the deployed code, of the same kind as the ARX adoption.
It restricts which implementation the theorem is about, not the attacker.

## What it does not settle

The deployment-inclusive rows (17P under FJv_Deployed) remain: the D188-P2
association rows and the twelve leaf bridges (extraction-assoc6, leaf-p6-1
running), L188 (F-AXIOM, D188-P), and joint real-byte non-vacuity
(fixture-tx2o, joint-fixture24 running). L154 is the per-query bound's own
parameter. The deployed 100-bit target is not established by this decision.

## Recommendation

Adopt FJv_Deployed.deployed as the headline statement and record it in the
security contract as a statement amendment ("the headline is stated for the
installed configuration: installed finish, boundaries and std; remaining
implementation inputs universally quantified"). Alternative: keep FJv_Top
as the headline and accept that L146 can never be removed from a statement
quantified over arbitrary terminals.

## Update, 2026-10-27 15:15 UTC: FJv_Deployed does not yet replay coherently

The coherent replay (replay-tops3, RPv_) compiled FJv_Top.deployed's whole
closure in the pinned cohort and booked L187 for it. FJv_Deployed did not
replay. Its ancestor FIr_FinishComparison fails to elaborate because it states
its observation over `verifier.Phase`, while the pinned cohort's retained
finish model expects `RPz7_PhaseIso.Phase` (evidence/replay-tops3-20261027/
RPv_0508-failure.json). That blocks 36 descendants, FJv_Deployed among them.

The recommendation stands as a choice of statement, but adoption now has a
precondition. FIr_FinishComparison must be reconciled to the pinned Phase
carrier (a proof change in a lead candidate, not a statement or
implementation change), and FJv_Deployed must then replay in the pinned cohort
with its kernel statement byte-compared to the one reviewed here. Until then,
its 83T/1P/13G is a cached-composition result and is not booked. The lead has
launched that reconciliation (prefix RPw_). If it shows the statement itself
must change, this packet will be revised before the owner is asked to decide.
