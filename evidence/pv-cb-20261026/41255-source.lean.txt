import R1Z.PV_CB_TupleProducerInvariant
import R1Z.PV_CB_CanonicalForward
set_option autoImplicit false
namespace R1Z.PV_CB_TupleProducerTotal
open Aeneas Aeneas.Std Result PV_CB_TupleProducerOffset

theorem step (row start count : Usize) (tweak_right : Bool) (bank : Bank)
    (i : Usize) (inside : i.val < 16) (limbs : Array Limb 16#usize) (vl : Valid limbs) :
    ∃ out, PV_CB_TupleProducerStep.step row start count tweak_right bank i limbs = ok out ∧ Valid out := by
  obtain ⟨value,hv,vv⟩ := canonical tweak_right i count
  obtain ⟨out,hout,vout⟩ := PV_CB_CanonicalUpdate.update ValidLimb limbs i
    (.Cell {bank,cell := {row := UScalar.cast .U16 row,column := UScalar.cast .U8 (Usize.wrapping_add start i)}} value)
    inside vl vv
  refine ⟨out,?_,vout⟩
  simpa only [PV_CB_TupleProducerStep.step,hv,lift,bind_tc_ok] using hout

theorem finite (row start count : Usize) (bound : count.val ≤ 16)
    (tweak_right : Bool) (bank : Bank) (fuel : Nat) (i : Usize)
    (limbs : Array Limb 16#usize) (rank : i.val+fuel=count.val) (vl : Valid limbs) :
    ∃ out, PV_CB_ForwardLoop.finite (PV_CB_TupleProducerStep.step row start count tweak_right bank)
      fuel i limbs = ok out ∧ Valid out :=
  PV_CB_CanonicalForward.finite Valid (PV_CB_TupleProducerStep.step row start count tweak_right bank) count
    (fun i hi state valid => step row start count tweak_right bank i (by omega) state valid)
    fuel i limbs rank vl

theorem source (row start count : Usize) (bound : count.val ≤ 16)
    (tweak_right : Bool) (bank : Bank) (limbs : Array Limb 16#usize) (vl : Valid limbs) :
    ∃ out, PV_CB_TupleProducerLoop.loop (PV_CB_ForwardRange.between 0#usize count)
      row start count tweak_right bank limbs = ok out ∧ Valid out := by
  obtain ⟨out,hr,vr⟩ := finite row start count bound tweak_right bank count.val 0#usize limbs (by simp) vl
  exact ⟨out,(PV_CB_TupleProducerLoop.finite row start count tweak_right bank count.val
    0#usize count limbs (by simp)).trans hr,vr⟩
#print axioms step
#print axioms finite
#print axioms source
end R1Z.PV_CB_TupleProducerTotal
