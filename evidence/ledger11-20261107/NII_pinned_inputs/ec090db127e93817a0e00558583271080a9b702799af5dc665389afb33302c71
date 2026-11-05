import NGL_DistinctStep
set_option autoImplicit false
noncomputable section
namespace NHD_DistinctAssociation
open Aeneas Aeneas.Std Result ControlFlow
attribute [local instance] Classical.propDecidable
abbrev PE := NGL_DistinctStep.PE
abbrev Account := NGL_DistinctStep.Account

def cut (duplicate : Bool) (previous : Usize) :
    Result (core.result.Result Unit PE × Usize) :=
  if duplicate then ok (.Err .InvalidArgument,previous)
  else do let next ← previous + 1#usize; ok (.Ok (),next)

def decode (packet : core.result.Result Unit PE × Usize) :
    ControlFlow Usize (Option (core.result.Result Unit PE)) :=
  match packet.1 with
  | .Err e => done (some (.Err e))
  | .Ok _ => cont packet.2

theorem increment (previous : Usize) (small : previous.val < 7) :
    previous + 1#usize = ok (Usize.wrapping_add previous 1#usize) := by
  have spec := Usize.add_spec (x := previous) (y := 1#usize) (by scalar_tac)
  obtain ⟨next, returned, value⟩ := WP.spec_imp_exists spec
  have wrapped := NFQ_ZeroPrimitives.wrap_add previous 1#usize
    (by change previous.val+1 ≤ 4096; omega)
  have same : next = Usize.wrapping_add previous 1#usize := by scalar_tac
  simpa only [same] using returned

/-- Decode the complete native iteration packet into the emitted loop control.
The increment bound follows from the same inner-loop invariant. This is a model
association, not a source-to-ELF or pointer-carrier hypothesis. -/
theorem associate {N : Usize} (ops : AdapterRw.Ops) (a : Array Account N)
    (index previous : Usize) (small : N.val ≤ 7)
    (inIndex : index.val < a.val.length) (inPrevious : previous.val < index.val) :
    (do let packet ← cut (decide ((a.val[previous.val]'(by omega)).key =
           a.val[index.val].key)) previous
        ok (decode packet)) =
      AdapterRw.r1_pool_adapter.owned.require_distinct_accounts_loop0_loop0.body
        (NGL_ReadonlyModel.install ops) a index previous := by
  have bound : previous.val < 7 := by have size := a.property; omega
  rw [NGL_DistinctStep.step ops a index previous inIndex inPrevious]
  by_cases same : a.val[previous.val].key = a.val[index.val].key
  · simp only [same,decide_true,cut,if_true,bind_tc_ok,decode]
  · simp only [same,decide_false,cut,Bool.false_eq_true,if_false,increment previous bound,
      bind_tc_ok,decode]

#print axioms increment
#print axioms associate
end NHD_DistinctAssociation
