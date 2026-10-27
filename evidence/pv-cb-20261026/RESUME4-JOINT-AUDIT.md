# Final focused joint axioms audit

All100 Lean attempts are spent:77 passing,23 rejected/stopped. IDs38300–38406
were consumed, including7 noncharged preflights. Never reuse any of these IDs.
The last3 charged attempts were38404–38406. No further Lean compilation is
authorized under this budget. Next unused ID38407 is recorded only for handoff.

Frozen focused manifest: RESUME4-FOCUSED-MANIFEST.json, validated before audits.
This audits the23-row candidate dictionary plus the checked resume4 helpers;
it is not a complete frozen privacy manifest or full transitive-source replay.
Previously compiled transitive dependencies retain their existing trust status.

|attempt|target|exit|wall|peak RSS KiB|swap|declarations|source revision|
|---:|---|---:|---|---:|---:|---:|---|
|38404|R1Z/PV_CB_Resume4JointAudit1|0|0:01.70|4283944|0|64|5caf54e39440545f09b3b9c4694284edc7e039a7|
|38405|R1Z/PV_CB_Resume4JointAudit2|0|0:01.91|4284528|0|134|5caf54e39440545f09b3b9c4694284edc7e039a7|
|38406|R1Z/PV_CB_Resume4JointAudit3|0|0:01.68|4283664|0|28|5caf54e39440545f09b3b9c4694284edc7e039a7|

Every audited declaration is free of nonstandard axioms; the union is
{propext, Classical.choice, Quot.sound}. Full #print axioms output, direct
object hashes, exact source hashes and capped launcher settings are in each
numbered receipt. Lean -M7000, memory6G/8G, swap0; unchanged restored launcher
actually uses TasksMax64 (its header comment still says128).

77 accepted objects were copied into this job's own lean-objects cache;
RESUME4-RETAINED-LEAN-CACHE.json identifies every object/source hash. No shared
source/object is mutated by cache retention. No fresh source law was added,
no premise removed, and no endpoint/deployment condition changed.161 previously
published PV_CB source files remain byte-identical to ff8096896d.
