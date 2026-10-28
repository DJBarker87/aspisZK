import NCO_Inner
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace NCO_Outer
attribute [local instance] Classical.propDecidable

theorem division (payload : Slice U8) : ∃ count : Usize,
    Slice.len payload / 32#usize = ok count ∧ count.val = payload.val.length/32 := by
  obtain ⟨count,call,value⟩ := UScalar.div_spec (Slice.len payload) (y := 32#usize) (by scalar_tac)
  exact ⟨count,call,value⟩

theorem advance (i : Usize) (bound : i.val < 116) : ∃ successor : Usize,
    i + 1#usize = ok successor ∧ successor.val = i.val+1 := by
  have spec : (i+1#usize : Result Usize) ⦃ x => x.val=i.val+1 ⦄ := by
    apply UScalar.add_spec <;> scalar_tac
  exact WP.spec_imp_exists spec

theorem step (payload : Slice U8) (i : Usize)
    (cap : payload.val.length ≤ 3712) (hi : i.val < payload.val.length/32) :
    ∃ successor : Usize, successor.val = i.val+1 ∧
      NCO_ParserRef.validate_ref_loop0.body payload i =
        if NCO_Inner.GoodFrom payload i.val 0 then ok (.cont successor)
        else ok (.done (i,none)) := by
  obtain ⟨count,dc,vc⟩ := division payload
  obtain ⟨successor,call,value⟩ := advance i (by omega)
  have lt : i < count := by scalar_tac
  have inner := NCO_Inner.run payload i 0#usize successor cap hi (by decide) call
  have zero : (0#usize).val = 0 := by scalar_tac
  rw [zero] at inner
  refine ⟨successor,value,?_⟩
  simp only [NCO_ParserRef.validate_ref_loop0.body,dc,bind_tc_ok,lt,ite_true,inner]
  split_ifs <;> rfl

theorem done (payload : Slice U8) (i : Usize) (hi : payload.val.length/32 ≤ i.val) :
    NCO_ParserRef.validate_ref_loop0.body payload i = ok (.done (i,some (.Ok ()))) := by
  obtain ⟨count,dc,vc⟩ := division payload
  exact NCO_LoopSteps.outer_done payload i count dc (by omega)

#print axioms division
#print axioms advance
#print axioms step
#print axioms done
end NCO_Outer
