# Source-extraction obstruction in existing CPH runtime fixture

Kernel theorem `AspisR1.JFx_ExtractionObstruction.cph_fixture_not_extracted`:
for EVERY AdapterRw.Ops dictionary and hashv, the retained local CPH n1/n2
cannot satisfy S2W_DigestExtraction.AeneasExtraction. The stage1 equality is
universal over account lists. n1 accepts the empty list; the actual owned
caller cannot (proved by AdapterRw.Accepted.first_call inversion).

This is a definite incompatibility of that witness, not a claim that all
possible instances of CPH_Top.deployed are inconsistent. CPH_Nonvacuity already
warned that it proves runtime-only consistency. Its theorem remains valid.
Adding D188 to that same model is impossible; replacing its constant natives
with actual source functions requires a new acceptance proof.

JFx_001 failed before elaboration (missing Port5Q1_QueryBlock on the short
SInt2-001 search path). JFx_002 uses the retained CPP_L100 dependency path
in the SAME coherent SInt2 workspace and passes. This is an environment
correction, not an unchanged timeout/OOM retry. Exit 0; 5.815115195 s;
peak 5,314,780 KiB; swaps 0. Exact source/dependency hashes, revision,
command/cgroup limits and all printed axioms are in JFx_002/receipt.json.
All three new theorems use only propext, Classical.choice, Quot.sound.
No shipped source changed. Budget so far: 2/100 Lean; 0/10 Kani.

Before and after CPH_Top.deployed and Rc3_Top.deployed are unchanged.
Ledger delta: 0 premises removed, 0 added, 0 repackaging credits.
The requested complete joint fixture remains open; an attempted extension
of the existing local runtime witness has been ruled out.
