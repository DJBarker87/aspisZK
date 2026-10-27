Read-only authoritative ledger at a026fedee95d4f4eb6d4fd711f626ecb055e724e; imported historical counts are corrected without task discharge credit.

## L142 discharged and stacked, 2026-10-27 (stack1, FJv_)

`AspisR1.FJv_Top.deployed` = FJu_Top.deployed with native L142 and
F3Y_G_L142 also removed (port of FJs_; global owner obligation is now only
`FJu_Remaining.Endpoint`, last evaluation = terminal; `FJv_GlobalOwners.
weaken` from the FJu owners; native Outcome keeps only that semantic
hypothesis; conclusion unchanged; standard axioms). Lead review: definitions
read directly.

| Root | Actual antecedent | Deployment-inclusive |
|---|---|---|
| ARX_Root.deployed (adopted statement) | 83T/11P/13G | 89T/27P/13G |
| **FJv_Top.deployed (current proved top)** | **83T/3P/13G** | **89T/19P/13G** |
| FJv_Deployed.deployed (specialised; NOT adopted, owner decision pending) | 83T/1P/13G | 89T/17P/13G |

Remaining actual P on FJv_Top: native L146 and F3Y_G_L146 (these range over
the free terminal callback of the configuration binder and cannot be
removed without specialising the statement), and L154 (the adversary's
issued-query budget). FJv_Deployed specialises the configuration to
`IDa_Deployed.deployedConfiguration missing indexError reservation`
(installed finish, boundaries with terminal := FIq_Terminal.terminal, std;
the six residual inputs universally quantified with no law) and removes both
L146 rows; it is booked only if the owner adopts it. Deployed 100-bit
target: not yet established.

## L187 booked for FJv_Top, 2026-10-27 (replay-tops3, RPv_); FJv_Deployed does not replay

L187 (coherent frozen replay; deployment-only P row) is discharged for
`AspisR1.FJv_Top.deployed` and only for that root. In the single pinned
workspace (/home/dombarker/project-offloads/codex-cx-replay-dry-20261026,
ordered LEAN_PATH in evidence/replay-tops3-20261027/RPv_PIN-NOTES.md), the
replay-dry/RPz8/RPt/RPu/RPv chain compiled the complete import closure of the
root:
- 6,438 repository modules plus pinned Mathlib.Tactic.Abel;
- RPv_ contributed the final 414 contexts, with 980 of 981 attempts passing;
  the single failure is the FJv_Deployed vertex below, outside this closure;
- one capped scope at a time, every receipt recording target, exit, wall,
  RSS, swap and revision.

The fresh complete kernel statement is byte-identical to
evidence/stack1-20261027/FJv_after_top.kernel.lean.txt (SHA256
4aff3c96...8fee). Only propext/Classical.choice/Quot.sound occur, all 180
formatter records are unreachable, and declaration audits cover every fresh
context with no nonstandard axiom. This is a replay of the cached-object
closure in one pinned cohort, which is what L187's criterion asks for. It is
not the source-to-ELF correspondence or the final trust and dependency audit
(L188, still open). Any new headline root needs its own L187 replay.

| Root | Actual antecedent | Deployment-inclusive |
|---|---|---|
| ARX_Root.deployed (adopted statement) | 83T/11P/13G | 89T/27P/13G |
| **FJv_Top.deployed (current proved top)** | **83T/3P/13G** | **89T/18P/13G** |
| FJv_Deployed.deployed (specialised; NOT adopted; does NOT replay, see below) | 83T/1P/13G | 89T/17P/13G (L187 not booked) |

FJv_Deployed finding: in the same pinned cohort, FIr_FinishComparison (an
ancestor of FJv_Deployed, outside FJv_Top's closure) fails to elaborate. At
lines 44:66 and 61:74 its observation has type
`Option (verifier.Phase -> Result Unit)`, but the retained FinishModel.finish
and S1SemanticFinishBounds.finish_success expect
`Option (RPz7_PhaseIso.Phase -> Result Unit)`. This blocks 36 descendants,
including FJv_Deployed (evidence/replay-tops3-20261027/RPv_0508-failure.json).
FJv_Deployed was therefore compiled in a cohort that differs from the pinned
one at the Phase carrier. Its 83T/1P figure is a cached-composition result
until it is reconciled and replayed. Deployed 100-bit target: not yet
established.
