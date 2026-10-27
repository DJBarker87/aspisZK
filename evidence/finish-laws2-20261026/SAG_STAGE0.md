# Finish laws second continuation

Base 9a00289da28a72263c02642fc1dc359d4e83294d; branch codex/cx-finish-laws2-20261026.
Read the governing Security and proof discipline, common/local rules, S2 ownership,
lead plan, diagnosis, route B addendum, S2LeadInterface, SAF handoff/31-row table,
SInt2 host handoff and Rc3 ledger method. Session A candidate sources are read-only.

Baseline counted theorem SAF_Deployed.deployed extends Rc3_Top.deployed:
82T+94P actual; 88T+107P actual plus non-alias deployment. Nineteen of the
31 finish families were previously removed. Twelve remain, including two
universally identical quarter laws (round bytes/polynomial do not occur).

First stage: prove round0 quarter from the retained round1 quarter and compose
that exact redundancy removal to SAG_Deployed.deployed. This is reuse of an
existing law, not concrete arithmetic verification. Preserve every source,
model, witness, guard, failure event and trust item. Investigate concrete native
bindings separately; do not claim an arbitrary FinishOps has finite-field laws.

Budget: at most 100 Lean invocations including dependencies; 20 Kani. One
scope per job, MemoryHigh6G/MemoryMax8G/SwapMax0/TasksMax64, Lean -M7000.
No shipped change or ELF rebuild trigger. No keys touched. No release claim.
