-- Inherited body, import-only deployed-cohort retarget.
import NCD_B_LPi_CheckedInputs
import NCD_B_LPi_DotPushTotal
set_option autoImplicit false
namespace AspisR1.LPi_PublicPush
open Aeneas Aeneas.Std Result LPi_FieldValues

theorem source (self : FIo_Native.fast_pairing.EbyKDot) (value : NE) (scalar : NQ)
    (hv : canonE value) (hq : canonQ scalar) (count : self.count.val < 4096) :
    ∃ out, FIo_Native.fast_pairing.EbyKDot.push self value scalar=ok (.Ok (),out) ∧
      out.count.val=self.count.val+1 := by
  have ca := LPi_CheckedInputs.canonical value.c0 hv.1
  have cb := LPi_CheckedInputs.canonical value.c1 hv.2
  have cq := LPi_CheckedInputs.canonical scalar hq
  obtain ⟨a,ha⟩ := LPi_DotPushTotal.source self.c0 _ _ ca cq
  obtain ⟨b,hb⟩ := LPi_DotPushTotal.source self.c1 _ _ cb cq
  have below : ¬self.count ≥ FIo_Native.fast_pairing.MAX_TERMS := by
    simp only [FIo_Native.fast_pairing.MAX_TERMS]
    scalar_tac
  have i0 : Array.index_usize (Array.make 2#usize
      [LPi_CheckedInputs.q value.c0,LPi_CheckedInputs.q value.c1]) 0#usize =
      ok (LPi_CheckedInputs.q value.c0) := rfl
  have i1 : Array.index_usize (Array.make 2#usize
      [LPi_CheckedInputs.q value.c0,LPi_CheckedInputs.q value.c1]) 1#usize =
      ok (LPi_CheckedInputs.q value.c1) := rfl
  refine ⟨⟨a,b,Usize.wrapping_add self.count 1#usize⟩,?_,?_⟩
  · simp only [FIo_Native.fast_pairing.EbyKDot.push,if_neg below,
      LPi_CheckedInputs.from_wide,bind_tc_ok,LPi_CheckedInputs.checked scalar hq,
      core.result.Result.Insts.CoreOpsTry.branch,i0,i1,ha,hb,lift]
  · rw [Usize.wrapping_add_val_eq]
    apply Nat.mod_eq_of_lt
    have lim := (4096#usize).hSize
    change 4096 < UScalar.size .Usize at lim
    change self.count.val+1 < UScalar.size .Usize
    omega

#print axioms source
end AspisR1.LPi_PublicPush
