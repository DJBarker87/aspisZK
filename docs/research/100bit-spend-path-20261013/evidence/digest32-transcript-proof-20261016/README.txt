Actual Digest32 constructor and admitted-step proofs; read/hash verifier only.

Five checked declarations in AspisR1PublicPreparation.TranscriptStep:
new_of_length: successful Usize->U32 conversion gives the exact five-slice constructor call and initial state/hash/next0.
new_success: actual constructor success derives that conversion, digest success and exact returned transcript.
wrong_row: mismatch returns RowOrder and the same transcript.
step_of_add: matching row plus checked arithmetic gives exact ordered absorb, read1, read2 binds, both reads on absorbed state.
step_success: admitted row.val<=26 and actual success derive row match, tag160+row, nextrow+1, all three exact digest successes and returned block/state/hash carry.

All five audits contain only propext/Classical.choice/Quot.sound. proof-b exit0,1.812s,peakRSS2661556KiB,sampled cgroup631050240B,process/cgroup swap0,6Ghigh/8Gmax. proof-a exit1 and sorryAx audit are retained as failure only; correction normalizes the U8 numeral1 projection, without a statement/limit change. Complete source snapshots, commands, runtime/object/import keys and raw logs are retained.

The two adapted import receipts/artifacts are byte-bound to C's naming archive b634c0cd..., original emitted Funs remains unchanged, and no predecessor was recompiled here. Exact source base9cf712b05, Rustb92. No production, test or native-gate change. No full33 caller, Observer, hbytes/htyped/ha/C2 provenance, arbitrary effectful callback, syscall/R16 or CU conclusion.

Host: /home/dombarker/project-offloads/aspis-r1-digest32-transcript-proof-20261016/{sources,objects,successful-targets,runs/proof-a,runs/proof-b}; external-inputs-proof.json and import-source-audit.json pin exact imported artifacts.
