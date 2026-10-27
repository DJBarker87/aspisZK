import XSe_ValidatorBody
open Aeneas Aeneas.Std Result ControlFlow
set_option autoImplicit false
namespace XSe_ValidatorIter
open XSe_ValidatorBody
abbrev E := XSe_ValidatorStage.OldError
def next (i : Usize) : Result Usize := i+1#usize
def stage (row : U8) := XSe_ValidatorStage.old row

def state (iter : Iter) : List (Slice U8) × Usize := (iter.iter.chunks,iter.count)
def flow : ControlFlow Iter (core.result.Result Unit E) →
 ControlFlow (List (Slice U8) × Usize) (core.result.Result Unit E)
 | .done r => .done r
 | .cont s => .cont (state s)
/-- Projection preserves each entire emitted loop step and its checked count. -/
theorem source (row : U8) (iter : Iter) :
 XRo_Join_Carriers.mapR flow (body row iter)=
 XSe_EnumeratedDriver.body next (stage row) (state iter) := by
 rcases iter with ⟨⟨chunks,remainder⟩,i⟩
 cases chunks with
 | nil => rfl
 | cons chunk rest =>
   unfold body core.iter.adapters.enumerate.IteratorEnumerate.next
   simp only [core.slice.iter.IteratorChunksExact.next,bind_tc_ok]
   unfold XSe_EnumeratedDriver.body state next stage
   simp only [bind_assoc_eq,XRo_Join_Carriers.mapR_bind]
   congr 1
   funext count
   dsimp! only
   simp only [bind_tc_ok,XRo_Join_Carriers.mapR_bind]
   congr 1
   funext status
   cases status <;> rfl
#print axioms source
end XSe_ValidatorIter
