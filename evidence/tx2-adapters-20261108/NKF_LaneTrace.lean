import NJH_LaneIterator
import NKF_BoxModel
set_option autoImplicit false
noncomputable section
namespace NKF_LaneTrace
open Aeneas Aeneas.Std Result
abbrev Node := NJD_LaneStep.Node
abbrev Frontier := Fin 20 → Node
abbrev Reply := NJD_LaneStep.Reply
attribute [local instance] Classical.propDecidable
/-- One actual lane-loop continuation: decode error leaves the selected node
unchanged; empty-subtree rejection occurs AFTER the assignment. -/
def iteration {F : Type} (empty : Node) (occupied : Bool) (before : Frontier)
 (level : Fin 20) (raw : core.result.Result Node F) : Reply × Frontier :=
 match raw with
 | .Err _ => (.Err .InvalidAccountData,before)
 | .Ok node =>
   ((NJD_LaneStep.step empty occupied (before level) (.Ok node)).1,
    NJD_LaneStep.write before level node)

/-- Rule-B model induction, with explicit call-prefix log and abort suffix.
Native association and SAME-byte digest arguments remain separate obligations. -/
def run {F : Type} (empty : Fin 20 → Node) (occupied : Fin 20 → Bool)
 (raw : Fin 20 → core.result.Result Node F) :
 List (Fin 20) → Frontier → Reply × Frontier × List (Fin 20)
 | [],before => (.Ok (),before,[])
 | level::rest,before =>
   let (reply,after) := iteration (empty level) (occupied level) before level (raw level)
   match reply with
   | .Err e => (.Err e,after,[level])
   | .Ok _ =>
     let (result,final,calls) := run empty occupied raw rest after
     (result,final,level::calls)

theorem iteration_frame {F : Type} (empty : Node) (occupied : Bool)
 (before : Frontier) (level other : Fin 20) (raw : core.result.Result Node F)
 (different : other ≠ level) :
 (iteration empty occupied before level raw).2 other = before other := by
 cases raw with
 | Err e=>rfl
 | Ok node=>exact NJD_LaneStep.frame before level other node different

theorem error_no_write {F : Type} (empty : Node) (occupied : Bool)
 (before : Frontier) (level : Fin 20) (error : F) :
 iteration empty occupied before level (.Err error)=
  (.Err .InvalidAccountData,before) := rfl

theorem rejected_write {F : Type} (empty node : Node) (before : Frontier)
 (level : Fin 20) (different : node≠empty) :
 iteration empty false before level (.Ok node : core.result.Result Node F)=
  (.Err .InvalidAccountData,NJD_LaneStep.write before level node) := by
 simp only [iteration,NJD_LaneStep.reject_after_write empty (before level) node different]

theorem loop_frame {F : Type} (empty : Fin 20 → Node) (occupied : Fin 20 → Bool)
 (raw : Fin 20 → core.result.Result Node F) (levels : List (Fin 20))
 (before : Frontier) (other : Fin 20) (outside : other ∉ levels) :
 (run empty occupied raw levels before).2.1 other=before other := by
 induction levels generalizing before with
 | nil=>rfl
 | cons level rest ih=>
   have different : other≠level := by intro same;exact outside (by simp [same])
   have away : other∉rest := by intro mem;exact outside (by simp [mem])
   have frame:=iteration_frame (empty level) (occupied level) before level other (raw level) different
   cases stepEq : iteration (empty level) (occupied level) before level (raw level) with
   | mk reply after=>
     rw [stepEq] at frame
     cases reply with
     | Err e=>simpa only [run,stepEq] using frame
     | Ok u=>
       simpa only [run,stepEq] using (ih after away).trans frame

theorem abort_no_suffix {F : Type} (empty : Fin 20 → Node) (occupied : Fin 20 → Bool)
 (raw : Fin 20 → core.result.Result Node F) (level : Fin 20) (rest : List (Fin 20))
 (before after : Frontier) (e : NKF_BoxModel.PE)
 (stopped : iteration (empty level) (occupied level) before level (raw level)=(.Err e,after)) :
 run empty occupied raw (level::rest) before=(.Err e,after,[level]) := by
 simp only [run,stopped]

set_option pp.proofs false in
#print loop_frame
#print axioms iteration_frame
#print axioms error_no_write
#print axioms rejected_write
#print axioms loop_frame
#print axioms abort_no_suffix
end NKF_LaneTrace
