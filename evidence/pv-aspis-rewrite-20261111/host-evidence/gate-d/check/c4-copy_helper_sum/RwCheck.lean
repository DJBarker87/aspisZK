import ProverPin2.Funs
open Aeneas Aeneas.Std Result ControlFlow Error
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000
set_option maxRecDepth 2048

namespace ProverPin2
namespace RW
noncomputable section

-- block emitted by tool k2 (7271db7e), sha256 ed843f17fd3ba3849f3da2928eb000d319b857ee391395360ebff0d8ef00c710, source ['/home/dombarker/project-offloads/codex-pv-aspis-rewrite-20261111/src-rw/crates/aspis-statement/src/state_only_semantic.rs', 593, 596]
def aspis_statement.state_only_semantic.state_only_copy_helper_sum_loop.body
  (i : Std.Usize) (h1 : Slice aspis_core.field.QM31)
  (sum : aspis_core.field.QM31) (row : Std.Usize) :
  Result (ControlFlow (aspis_core.field.QM31 × Std.Usize)
    aspis_core.field.QM31)
  := do
  if row < i
  then
    let q ← Slice.index_usize h1 row
    let sum1 ← aspis_core.field.QM31.add sum q
    let row1 ← lift (Std.Usize.wrapping_add row 1#usize)
    ok (cont (sum1, row1))
  else ok (done sum)

-- block emitted by tool k2 (7271db7e), sha256 ab6423918b79b2b20f009515b352a836b03f9323e9b618d6961e6bfbcf747aa2, source ['/home/dombarker/project-offloads/codex-pv-aspis-rewrite-20261111/src-rw/crates/aspis-statement/src/state_only_semantic.rs', 593, 596]
def aspis_statement.state_only_semantic.state_only_copy_helper_sum_loop
  (i : Std.Usize) (h1 : Slice aspis_core.field.QM31)
  (sum : aspis_core.field.QM31) (row : Std.Usize) :
  Result aspis_core.field.QM31
  := do
  loop
    (fun (sum1, row1) =>
      aspis_statement.state_only_semantic.state_only_copy_helper_sum_loop.body
      i h1 sum1 row1)
    (sum, row)

-- block emitted by tool k2 (7271db7e), sha256 2d5011fa28543e9ff45a18fcab703eda52099545c23a7ea4043345ef2f3e2797, source ['/home/dombarker/project-offloads/codex-pv-aspis-rewrite-20261111/src-rw/crates/aspis-statement/src/state_only_semantic.rs', 583, 583]
def aspis_statement.state_only_semantic.state_only_copy_helper_sum
  (h1 : Slice aspis_core.field.QM31) :
  Result (Option aspis_core.field.QM31)
  := do
  let i := Slice.len h1
  let i1 ← aspis_statement.trace_v4.TRACE_ROWS
  if i != i1
  then ok none
  else
    let sum ←
      aspis_statement.state_only_semantic.state_only_copy_helper_sum_loop i1 h1
        aspis_core.field.QM31.ZERO 0#usize
    ok (some sum)

end
end RW
end ProverPin2

example : type_of% @ProverPin2.RW.aspis_statement.state_only_semantic.state_only_copy_helper_sum = type_of% @ProverPin2.aspis_statement.state_only_semantic.state_only_copy_helper_sum := rfl
#check @ProverPin2.RW.aspis_statement.state_only_semantic.state_only_copy_helper_sum
#print axioms ProverPin2.RW.aspis_statement.state_only_semantic.state_only_copy_helper_sum
-- 3 carried blocks, 0 new opaque items, 1 signature checks
