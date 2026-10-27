# TX1 query/flush/writer integration

Branch codex/cx-tx1-query-20261025; starting revision
5c512bdad39fef19f9f18a0b675495d94a77b9d7. S2 remains open.

Binding rules read: root AGENTS.md including Security and proof discipline,
r1p-common.txt and local-lean.txt; S2 ownership/lead/diagnosis packet, route B
adoption, S2LeadInterface, SOUND-INT and SInt2/op3/op4 handoffs.
The older S2 packet paths resolve under docs/research/100bit-spend-path-20261013.

Interpretation: op6/query, op9/flush and op8/writer are VTop slot numbers.
The actual Op4P base uses AspisR1CurrentCaller.Ops, where these are op7,
op17 and op16 respectively. They have independent nominal carriers. Installing
VTop functions into numerically matching CurrentCaller fields would be wrong.
Prove the carrier transport and slot correspondence explicitly.

Stages: (1) audit/target; (2) reversible carriers and concrete body installation;
(3) same-accepted-pair extension and remaining premise audit; (4) handoff.
Each completed stage is committed locally, without push.

Limits: at most 80 Lean attempts including dependency builds, 40 Kani;
-M7000, 6G high/8G max/swap0/tasks64, no package replay, no unchanged timeout
or memory-kill retry. Existing S2W launchers and coherent SInt2 objects only.
No source/ELF/key changes are planned. Only Tx1Q_ new modules are allowed.

Stage 2 checked: reversible CurrentCaller/Stage2 carrier maps; exact installed
query/flush/writer slots and restored other fields; source initial/pending/geometry
choices; Q1 total query installation compatibility; suffix inversion; witness
construction from ONE accepted source call and from Op4P's SAME SourceCuts.
No equality of arbitrary dictionaries is assumed. Source/P6 adoption boundaries
are retained; in particular the writer is still explicitly the selector reference.

Host reuse: coherent SInt2 and Op4P paths precede the unchanged Q1/Port4 cached
objects in LEAN_PATH. Direct selected objects are hashed in every receipt. This
successful combined import is a focused cached check, not a coherent release
rebuild. Rebuilding 84 missing Q1 dependency modules from scratch would exceed
this task's 80-attempt limit; no such rebuild was launched. No cache object or
existing source was overwritten. The inherited S2W launchers are unchanged.
