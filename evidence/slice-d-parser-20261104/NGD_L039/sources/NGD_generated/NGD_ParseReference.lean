import NGD_AtG.Funs
import NGD_ErrorPort
import NGD_ParseCut
import NGD_AtShape
import NGD_WrapFacts
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace NGD_ParseReference

def mapResult {α β : Type} (f : α → β) : Result α → Result β
  | .ok x => .ok (f x)
  | .fail e => .fail e
  | .div => .div

theorem map_bind {α β γ : Type} (f : β → γ) (r : Result α) (k : α → Result β) :
    mapResult f (r >>= k) = (r >>= fun x => mapResult f (k x)) := by
  cases r <;> rfl

theorem map_if {α β : Type} (f : α → β) (p : Prop) [Decidable p]
    (yes no : Result α) : mapResult f (if p then yes else no) =
      if p then mapResult f yes else mapResult f no := by split <;> rfl

theorem wrap_checked (x y z : Usize) (add : x + y = ok z) :
    Usize.wrapping_add x y = z := by
  have facts := UScalar.add_equiv x y
  rw [add] at facts
  exact NGD_WrapFacts.add x y z facts.2.1.symm

/-- Exact complete error carrier at the child cut. The child reply is arbitrary,
and every primitive read/failure is retained on both sides. -/
theorem framed_cut (row tag : U8) (size total : Usize) (record : Slice U8)
    (reply : core.result.Result Unit NGD_AtG.Error)
    (shape : NGD_AtG.shape row = ok (some (tag,size)))
    (add : 5#usize + size = ok total) :
    mapResult NGD_ErrorPort.mapError (NGD_AtG.parse_g row record reply) =
      NGD_ParseCut.invoke (fun _ _ => ok (NGD_ErrorPort.mapError reply)) row record := by
  have sourceShape : AspisR1PrefixAggregateParser.r1_wire.row_shape row = ok (some (tag,size)) := by
    rw [← NGD_AtShape.reference]; exact shape
  have wrap := wrap_checked 5#usize size total add
  cases reply <;>
    simp [NGD_AtG.parse_g,NGD_ParseCut.invoke,shape,sourceShape,add,wrap,lift,
      NGD_AtG.core.option.Option.ok_or,AspisR1PrefixAggregateParser.core.option.Option.ok_or,
      core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
      map_bind,map_if,mapResult,NGD_ErrorPort.mapError,NGD_ErrorPort.toWire]
#print axioms map_bind
#print axioms map_if
#print axioms wrap_checked
#print axioms framed_cut
end NGD_ParseReference
