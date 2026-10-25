# Stage 1: value guards on the same run

Checked: WAdm_Arithmetic.calls/on_run propagate canonical rhs/power through
actual calls; WAdm_Public.reached derives public1880 from the same published
SourceCuts and the concrete caller snapshot; WAdm_Domain.on_run derives the
exact bounded certificate's value domain; WAdm_Inventory.on_run constructs
all canonical checkpoint fields on the same materialized state.

Retained SessionAPrepare is explicitly the immutable preparation owner's
contract on the same preparation return. It contains no query/writer output,
native/reference equality, or successful parent. SessionAPrimitives, including
line_canonical, stays the previously named owner contract. These owner fields
have not been instantiated here. No parser/model/authentication gate is needed
for mutable canonicality. Runtime/physical carrier and concrete native writer
substitution are NOT established by these value lemmas. Thus no top-level
premise removal or full native writer closure is claimed at this stage.

7/100 Lean attempts, 0/40 Kani. 001,002,005,006,007 passed; 003/004 failed local
alpha-index elaboration, fixed without changing the statement. All passing
theorems print only propext/Classical.choice/Quot.sound. Receipts include exact
command/revision/source/dependency hashes, exit, wall time, RSS and swap. No
memory kill or timeout; no caps changed; no shipped file changed. ELF pins
remain inherited. No package/full-manifest replay or unchanged Kani replay.
