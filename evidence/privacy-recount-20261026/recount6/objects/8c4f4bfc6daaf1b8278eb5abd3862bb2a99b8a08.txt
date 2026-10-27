# pv-reach3 continuation report (LOG D310)

Branch `codex/pv-reach-20261027`, exact worktree
`/Users/dominic/ZK/.worktrees/pv-reach`; resume head `f21491b422`.
**Target not yet established. V404 OPEN → OPEN; V405 OPEN → OPEN.**
No endpoint/deployment/T/shipped-code/key/shared-source changes, push or merge.

**Provenance and reuse.** Before the first compile, all 5,673 h4-manifest
objects matched. `h4-library-cohort.json` confirms all 236 library modules,
including exactly the 18 h3 deltas. The prior 33 checks are reused under h4;
old check targets were not rerun. Cache loss required fresh proof targets;
the new whole-client proof regenerated overlapping helper congruences. Libraries
were never rebuilt/substituted. Four project source pins were rechecked.

**Sets.** Actual S_transfer and S_withdrawal remain unestablished. The new
kernel-checked whole-caller **Result support overapproximation**, identical for
both shapes, is U={op0,…,op261}\{op13,op16,op17,op18,op85,op124,op238}.
`static-support.json` lists every field; U is not claimed reached/minimal.

**(a)** 1,048 named local fail/div absorption certificates cover traversed bind
contexts in all 74 suffixes and corresponding source functions. A separate
695-body scan finds no direct outer Result error recursor. Whole-source
invocation-to-error composition is **not proved**. `NoCatchBoundary.local_certificates_insufficient` checks this method limitation;
it is not a shipped counterexample.

**(b)** `NoCatchCore.exclusion_by_poisoning` proves the universal admitted,
outer-successful-input implication with congruence and invocation absorption
explicit. `ExcludedPoison.unchanged13/16/17/18/85/124/238` and
`ShapeExclusions.transfer/withdrawal` establish unconditional whole-caller
poisoned-Result equality. The actual invocation absorption instance remains
missing; no native fixture invocation exclusion is claimed.

**(c)** `ShapePoison.poisoned_entry` proves op233 poisoning forces failure on
every extracted input; `success_distinguishes` is conditional on supplied
success. No concrete native success witness or remaining-field minimality
witness was proved.

Native rejection/retry exhaustion inside outer `.ok (.Err …)` satisfies the
poison argument's outer-success condition. Outer failure equality alone gives
no exclusion; a different poison error can distinguish it. Divergence requires
an actual finite reached-prefix witness. `PoisonOutcomes` and `ShapeRejection`
record the precise constructor/control laws.

**Rows and boundary.** `row-definition-match.md` compares the unchanged
recorded definitions. Invocation composition, admitted-input exclusions and
minimality remain V404/V405 obligations; native fixture associations,
ordered effects and fidelity remain V163/V167 and underlying source/effect rows.
Exact inherited native hypotheses remain uninstantiated; non-vacuity is not
claimed. The remainder is more than ordering/native fidelity.

**Validation/stop.** Budget exhausted: 100/100 Lean total; prior 27 pass/6 fail,
new 65 pass/2 fail; zero Kani. IDs 36933–36999 sequential; zero refusals.
Failures 36933/36935 are retained; replacements changed dependencies/source.
36955's receipt classification was corrected without rerun. All scopes 6G/8G/swap0, TasksMax64,
Lean -M7000; maximum observed RSS 2,886,385,664 bytes, swaps zero.
All 2,852 printed new axiom reports are standard only.

| Audit target | ID | Exit | Wall seconds | Peak RSS bytes | Swap |
|---|---:|---:|---:|---:|---:|
| FinalAudit3A | 36997 | 0 | 2.203 | 2710466560 | 0 |
| FinalAudit3B | 36998 | 0 | 1.917 | 2703806464 | 0 |
| FinalAudit3C | 36999 | 0 | 1.447 | 2713329664 | 0 |

Audit source revision: `28d49ff10161a8cf2ac39ea11234dcbaf84ef389`.
`receipt-index.json` records every target, exit, wall, RSS, swap, revision,
source/dependency hash and full axioms result. The final new-proof manifest
import check passed once; no clean release/endpoint-closure replay is claimed.
Generators/source hashes validate; history is `commits-before-final.txt`.

**Next deliverable:** kernel-checked source-context coverage/composition,
then actual admitted-input poisoning exclusions and concrete non-vacuous
fixture minimality witnesses. Exact steps are in `next-deliverable.md`.
