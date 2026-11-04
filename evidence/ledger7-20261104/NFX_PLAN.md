# Ledger refresh 7 plan and scope

Pinned initial research/worker tip: 616c30e35be. Branch codex/cx-ledger7-20261104.
Only NFX-prefixed files in this evidence directory are written. No Kani,
extraction, shipped source, ELF, other worktree, key or cache cleanup.
Budget: 40 Lean/audit attempts, zero Kani and extraction; one admitted capped
scope at a time, MemoryHigh=6G, MemoryMax=8G, swap=0, TasksMax=64, Lean -M7000.

Stages, each committed:
1. Policy and input/validator inventory; exact committed evidence pins.
2. Replay unchanged predecessor validators on their own evidence, build the
   additive 587-row ledger, routes and current trust inventory. No name-based
   promotion; preserve denials and distinguish local from composed evidence.
3. Combined S/Q/D-closed certificate import with RPx_Deployed; raw NEP ax2
   traversal, eight fidelity fixtures, and full incoherence scan. Any dependency
   on defective legacy forest reopens affected packet rows to QUALIFIED.
4. Final additive mutation checks, artifact/source pins, findings and handoff.

Binding inputs read: root AGENTS.md including Security and proof discipline;
r1p-common.txt; local-lean.txt rules 1–17; S2 ownership/plan/diagnosis, route-B
adoption, S2LeadInterface, SInt2 handoff; vertical slice definition and NDT
rejection reasons; NFK workflow; current C3-BIN rulings including (y), (ax2),
(ad) corrected, (ae), (ab'), (af), runtime owner acceptance.

The ledger must preserve 100-bit per-attempt soundness, privacy and two
transactions. Target not yet established. RuntimeReturnData (nonempty scope),
RuntimeMemcmp, RuntimePersistence and P6/D188 option A stay explicit. L154 is a
statement parameter. Digest/error slots are 43/44 in the coherent cohort.
