# Port15DRIVER plan and interface

Assigned branch codex/cx-port15driver-20261024; base 21b33f3e7d.
No shipped source, protocol, trust, feature, target, key or ELF changes.

Before: Port12COUNT_Installed.checkpointChain_count bounds a four-call projection
by 1046. It is not Port1_Driver.stages. No finite bound holds for unrestricted
rest: op3 can emit 1162 asks and then fail.

After (intended, not yet established): for arbitrary rest R and w : Nat → Nat,
assume explicitly, for each delegated j in [3,4,6,7,9,10,11,12,17,19],
∀ {A} (call : VTop_Trace.Call A) H, operationId call = j →
  (eval H (R call)).1.length ≤ w j.
Prove actual TX1(k=10, obs=None), TX2_authenticated(obs=None), stages and rust
all-outcome bounds with Port9OR_Installed.implementation ops reserved unwrap R.
Whole-driver bound: 1046 +
  (2*w 3+w 4+2*w 6+w 7+2*w 9+2*w 10+2*w 11+w 12+w 17+w 19).
Derive 1161 only under the explicit weighted sum ≤115. No success, acceptance,
refinement or whole-driver bound is in these local premises. All arguments
remain universally quantified; no reached-domain invariant is assumed.
Actual saved.deref from TX1 feeds TX2. Actual Prepared/Accumulator replies feed
all later calls. Direct pure Results/library calls cost zero on every outcome.
Literal batch0 and batch1 bounds are reused without reducing physical bodies.

Workflow: smallest structural cost lemmas, TX1, TX2/driver, focused full
statement/import/axiom audit. No full manifest or build/extraction gates.
Inherited 219/240 charged (218 actual+1 preLean), at most 21 new attempts;
all reservations/failures retained. Reuse pinned host caches. Full hierarchy
admission fixtures precede launches; fresh admission under global lock;
6G/8G/no-swap/TasksMax64 independently verified before Lean. No local Lean.
Optional accounting composition only after actual control proof is green.

Concrete R/weights, source acceptance→recovery/parse/query/root/frame/no-hit,
CleanAcceptedModel, StoredCarrierBinding and primitive adoption stay open.
Both deployed targets not yet established. Security bound remains
(Q+34)*B+kappa(Q+1161)+2^-126+2^-454.
