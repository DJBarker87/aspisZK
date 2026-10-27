# Stage 1: compatible installed dictionaries

Rc3_Install.compatible proves the circle-source and NP6 std installations commute.
Rc3_Install.exact_scope proves equality with the original Rc2 configuration iff
its original circle slot was already the deployed source. No arbitrary dictionary
compatibility is assumed. All other slots retain Rc2's selected instance.

Rules and required S2 handoffs, diagnosis, interface, C3-BIN route-B addendum,
owner amendment and coherent SInt2 packet inspected. Only Rc3 files are written.
No new trust or shipped change. RuntimePersistence/frozen3 are approved; their
future integration is owned by concurrent jobs and is not claimed here.

Rc3_001 failed before elaboration: missing PAln_RowBounds search path, exit1,
0.602485328s,1542296KiB,swap0. Rc3_002 selects SAP_101's complete pinned search
path (parse-align and parse-sem caches); exit0,2.574672301s,5301192KiB,swap0.
Both admitted scopes use 6G/8G/swap0/tasks64 and -M7000. No dependency build,
resource timeout/kill or cap increase. Full source revision/hash, command,
dependency/tool fingerprint and standard-axiom lines are in receipts. Six new
lemmas print only propext/Classical.choice/Quot.sound. Used2/60 Lean,0/0 Kani.
