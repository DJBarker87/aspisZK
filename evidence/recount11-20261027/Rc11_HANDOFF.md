# Rc11 handoff: mechanical admitted-root recount

Candidate: `AspisR1.ARX_Root.deployed`, unchanged, proved but unadopted.
Adopted root: `AspisR1.Rc10_Top.deployed`, unchanged. No new proof.
Branch: `codex/cx-recount11-20261027`; start `eb7eab86b9e06595ce4e37a7f20fe44616d845e1`.
This is the provisioned branch; the prompt's earlier suffix was 20261026.

## Delivered

- `lean/Rc11_Candidate.lean`: both COMPLETE kernel signatures, named ARX
  declaration and axioms audits. No wrapper theorem or adoption.
- `Rc11_BEFORE.lean.txt`, `Rc11_AFTER.lean.txt`, `Rc11_statement.diff`:
  every binder change and byte-identical conclusion schema after `let select`.
- `lean/Rc11_Inventory.lean`: all 44 Rc10 family inventories freshly printed;
  every retained block matches modulo whitespace. Changed adversary, induced
  queries, admitted support/image, carriers and conditional consumers printed.
- `lean/Rc11_Boundaries.lean`: further unfolding of P1/syscall, query/cylinder
  agreement, admitted mean/charge, failure functional and numeric definitions.
- `Rc11_LEDGER.md`, `Rc11_premises.json`, `Rc11_row-diff.json`: all 119 Rc10
  rows enumerated side by side; 116 retained, including specialized L154.
- `design/SECURITY-CONTRACT-ARX-AMENDMENT-DRAFT-20261027.md`: draft only;
  admitted image, issued-work definition, exact statement change, constants,
  positive margin and remaining gates. Authoritative contract/ledger untouched.

## Recount and qualification

| Scope | Rc10 T/P/G/C | Candidate T/P/G/C |
|---|---|---|
| Actual atomic antecedents/continuations | 83/12/13/0 | 83/11/13/0 |
| Deployment-inclusive, non-alias | 89/16/13/0 | 89/14/13/0 |

Removed L159, its alias L185, and L181's admitted experiment/native-prefix
association. The independent runtime and P binders are data, not extra P
credit. Added `a` and defined P/runtime have no atomic Prop fields. L154 is
the same budget specialized through `ARW_Induced.queries`; additions and
reclassifications are zero. Adopted delta is zero until owner approval.

No constant, carrier type, event constructor or conclusion schema differs.
Literal propositions differ through specialization of P/runtime; no equality
of the global unfiltered ART mean is claimed. Admission is zero extension
with original weights, not conditioning. The root's fixed native tuple is
not asserted to witness every adversary's execution. L081 remains GLOBAL
P1Realization in both fixed-root antecedents; query-restricted coverage is a
separate theorem, not a silent weakening of that retained trust boundary.

Non-vacuity remains conditional: `ARX_Nonvacuity.conditional` transports the
original JFx proof/public bytes from a SAME installed SupportedEntry and
consistent cylinder. It does not construct the missing full real-byte native
pair or jointly inhabit all release hypotheses. Exact partial predecessors
are retained in ARX_ROOT_COMPARISON; no completed JFp_/JFo_ pair is invented.

Remaining P: ten independent native/global finish families, L154, L166,
L187 and L188. Full native pair and owner adoption remain open.
**The deployed 100-bit target is not yet established.**

## Validation and freeze

3/20 Lean attempts, all pass; 0/0 Kani. Total wall 8.200638087 seconds,
max peak RSS 5558572 KiB, swap 0. Each used one scope at a time with
MemoryHigh=6G, MemoryMax=8G, MemorySwapMax=0, TasksMax=64, Lean -j1 -M7000.
No reservation retries, timeout, memory kill, cap raise or dependency build.
Both roots and all printed consumers/definitions use only standard axioms
`propext`, `Classical.choice`, `Quot.sound`. Exact target, command, source
revision/hash, selected dependency fingerprint, exit, time, RSS, swap,
cgroup and full axioms lines are in Rc11_attempts.jsonl and Rc11_00*/.

Rc11_root-pins.json matches both reused root source/object hashes to retained
acceptance evidence. This is focused cached auditing, not a coherent release
rebuild. Own Rc11 objects were hashed and removed after final use; shared
cached objects were retained. No binaries committed.

No shipped or cfg(kani) source changed, so no SBF rebuild trigger fired.
Inherited ELF pins, not freshly reproduced:

- default `f8c0ec72621fd5029a97d796c4a3623d0dc44a8e7074122372f9872915d143d4`
- devnet `63ad3e9cc096dcbb55b3ca7ac7c8e89e6a845796ab5e4f5b7d15db96f3784299`
- Pool `121f3e29741f510e6dc42d0345fc3c36217600f0be337094855c4a9da2581548`

No package replay, Rust/Kani/SBF work, sibling-worktree edits, key changes,
adoption, merge or push. Stage commits are local with plain messages.
