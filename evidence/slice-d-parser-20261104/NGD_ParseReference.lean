import NGD_AtG.Funs
import NGD_ErrorPort
import NGD_ParseCut
import NGD_AtShape
import NGD_WrapFacts
import NFU_RowDomains
set_option autoImplicit false
open Aeneas Aeneas.Std Result WP
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

theorem map_ok {α β : Type} (f : α → β) (x : α) : mapResult f (ok x) = ok (f x) := rfl
theorem map_fail {α β : Type} (f : α → β) (e : Aeneas.Std.Error) : mapResult f (fail e : Result α) = fail e := rfl
theorem map_div {α β : Type} (f : α → β) : mapResult f (div : Result α) = div := rfl

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
  have wrapNat : (5 + size.val) % Usize.size = total.val := by
    have h := congrArg UScalar.val wrap
    change (Usize.wrapping_add 5#usize size).val = total.val at h
    rw [Usize.wrapping_add_val_eq] at h
    simpa using h
  cases reply <;>
    simp [NGD_AtG.parse_g,NGD_ParseCut.invoke,shape,sourceShape,add,wrap,lift,
      NGD_AtG.core.option.Option.ok_or,AspisR1PrefixAggregateParser.core.option.Option.ok_or,
      core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
      map_bind,map_if,map_ok,map_fail,map_div,wrapNat,NGD_ErrorPort.mapError,NGD_ErrorPort.toWire]
theorem invalid_cut (row : U8) (record : Slice U8)
    (reply : core.result.Result Unit NGD_AtG.Error)
    (shape : NGD_AtG.shape row = ok none) :
    mapResult NGD_ErrorPort.mapError (NGD_AtG.parse_g row record reply) =
      NGD_ParseCut.invoke (fun _ _ => ok (NGD_ErrorPort.mapError reply)) row record := by
  have sourceShape : AspisR1PrefixAggregateParser.r1_wire.row_shape row = ok none := by
    rw [← NGD_AtShape.reference]; exact shape
  simp [NGD_AtG.parse_g,NGD_ParseCut.invoke,shape,sourceShape,lift,
    NGD_AtG.core.option.Option.ok_or,AspisR1PrefixAggregateParser.core.option.Option.ok_or,
    core.result.Result.Insts.CoreOpsTry.branch,
    core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
    map_ok,NGD_ErrorPort.mapError,NGD_ErrorPort.toWire]

theorem shape_total (row : U8) : ∃ value, NGD_AtG.shape row = ok value := by
  unfold NGD_AtG.shape
  split
  all_goals repeat' split
  all_goals exact ⟨_,rfl⟩

/-- No final output or acceptance hypothesis: all rows, bytes and full child replies. -/
theorem all_inputs (row : U8) (record : Slice U8)
    (reply : core.result.Result Unit NGD_AtG.Error) :
    mapResult NGD_ErrorPort.mapError (NGD_AtG.parse_g row record reply) =
      NGD_ParseCut.invoke (fun _ _ => ok (NGD_ErrorPort.mapError reply)) row record := by
  obtain ⟨out,shape⟩ := shape_total row
  cases out with
  | none => exact invalid_cut row record reply shape
  | some pair =>
    rcases pair with ⟨tag,size⟩
    have bounds := NFU_RowDomains.parser_shape row tag size (by rw [← NGD_AtShape.reference]; exact shape)
    have spec : (5#usize + size : Result Usize) ⦃ out => out.val = 5 + size.val ⦄ := by
      apply UScalar.add_spec <;> scalar_tac
    obtain ⟨total,add,_⟩ := WP.spec_imp_exists spec
    exact framed_cut row tag size total record reply shape add
#print axioms invalid_cut
#print axioms shape_total
#print axioms all_inputs
#print axioms map_bind
#print axioms map_ok
#print axioms map_fail
#print axioms map_div
#print axioms map_if
#print axioms wrap_checked
#print axioms framed_cut
end NGD_ParseReference
