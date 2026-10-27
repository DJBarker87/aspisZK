import R1Z.PV_CBM_CellsReference
namespace R1Z.PV_CBM_CellsMaterializer
open Aeneas Aeneas.Std Result
set_option autoImplicit false
abbrev Cell := ProverRwFull.aspis_statement.trace_v4.TraceCell
abbrev LayoutError := PV_CBM_ReferenceRaw.aspis_statement.pool_v1.pair_tree_hiding.PoolV1PairHidingLayoutErrorV1

def snapshot {α : Type} (r : Result ((core.result.Result Unit LayoutError) × alloc.vec.Vec α)) :
    Result (core.result.Result (alloc.vec.Vec α) LayoutError) := do
  let (answer, out) ← r
  match answer with
  | .Ok _ => ok (.Ok out)
  | .Err error => ok (.Err error)

def callback : Result (core.result.Result (alloc.vec.Vec Cell) LayoutError) :=
  snapshot (PV_CBM_CellsRaw.reference.fill_cells (alloc.vec.Vec.new Cell))

theorem snapshot_ok {α : Type} (out : alloc.vec.Vec α) :
    snapshot (ok (.Ok (), out)) = ok (.Ok out) := rfl

theorem snapshot_error {α : Type} (error : LayoutError) (out : alloc.vec.Vec α) :
    snapshot (ok (.Err error, out)) = ok (.Err error) := rfl

theorem snapshot_failure {α : Type} (error : _) :
    snapshot (α := α) (fail error) = fail error := rfl

#print axioms snapshot_ok
#print axioms snapshot_error
#print axioms snapshot_failure
end R1Z.PV_CBM_CellsMaterializer
