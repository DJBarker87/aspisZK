# Scope and premise audit before implementation

Target: remove the arbitrary erased SDK read-log child from
`Op5T_Final.accepted_pair_claims_op5`, on its exact accepted pair, with
success-conditioned marks, then global first-commitment recovery.
No shipped-source change, new trust item, security-contract change, or
other-worker module change is authorized. SessionAPrepare may remain named.

Before: arbitrary `E`, `port : ChildConeJoin E dictionary`,
`firstMarks : Op5T_Marks.FirstMarks port`, `secondMarks : ...`.
Erasure fixes only the result. It does not fix any emitted reads.
Intended after: source-computed port and proved marks, with the same source
cuts and all predecessor conclusions. No existentially chosen unrelated pair.

Read the canonical nested design/interface files where the requested root
paths do not exist. Route B is AccountInfo/RefCell trust only. D188 binds
owned source functions and digest wrapper, and does not admit a whole child
trace. The existing syscall boundary is success-conditioned, not total.
The initial implementation will preserve that distinction and prove the
primitive source wrapper trace before attempting its caller composition.

Stage validation: read-only source/receipt audit; no compiler or Kani run.
No axioms audit applies yet. Frozen pins are inherited, not reproduced:
default f8c0ec72621fd5029a97d796c4a3623d0dc44a8e7074122372f9872915d143d4;
devnet 63ad3e9cc096dcbb55b3ca7ac7c8e89e6a845796ab5e4f5b7d15db96f3784299;
Pool 121f3e29741f510e6dc42d0345fc3c36217600f0be337094855c4a9da2581548.

Resource plan: reuse the supplied coherent host workspace unchanged cache;
only SdkC_ sources/objects/receipts are added. One module per attempt, -M7000,
6G high/8G max/swap0/tasks64. No package replay or heavy arithmetic.
