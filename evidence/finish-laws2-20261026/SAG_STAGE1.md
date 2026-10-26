# Shared quarter law composed

SAG_Deployed.deployed now compiles (SAG_013). Its configuration, outer binders,
actual cuts and successful source witnesses are unchanged from SAF_Deployed.
The only logical change is in SAG_FinishPrepared.Outcome: SAG_Arithmetic.Laws
contains the six arithmetic families boundary0,eval0,round1.{boundary,quarter,eval},pair.
SAG_Arithmetic.reconstruct supplies the omitted round0.quarter directly from
round1.quarter. This is removal of a redundant universally identical premise,
NOT verification of the retained quarter implementation law. Distinct round
boundary/evaluation laws and their source operands remain distinct.

Ledger method: L134 derived from retained L137, no replacement premise.
82T+94P -> 82T+93P actual; SessionA73->72; lead18/external3 unchanged.
88T+107P -> 88T+106P actual plus non-alias deployment. Relative to Rc3:
20 assigned families removed (19 inherited), 11 open. Semantic, matching and
dot laws are not removed; source interpretation remains open. Same non-vacuity
Facts and existing guards are retained by SAG_FinalResult; no unconditional
joint inhabitation of all remaining conditions is claimed.

13/100 Lean invocations, all exit0, standard axioms only; 0/20 Kani.
SAG_013 wall10.88119527202798s, peak5377524KiB, swap0; exact source/revision,
dependencies, command and cgroup limits in its receipt. No full replay.
Before attempt13 the reservation scanner saw another scope vanish while reading
cgroup.procs. No prover launched; waited30s and retried once per local rule6.
The retry admitted the scope. No launcher/monitor/admission code was modified.
No shipped/cfg(kani) source change; ELF rebuild trigger remains absent.
