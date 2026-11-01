import R1Z.PV_RunJoin_MaskPreparedTotal69
import PV_B3_Range117
set_option autoImplicit false
namespace R1Z.PV_RunJoin_MaskRangeTotal69
open Aeneas Aeneas.Std Result PV_B3_Copy_117 PV_B3_Range117 PV_RunJoin_MaskFieldTotal69

theorem scatter {n : Usize} (input : Array Q n) (exponents : Array U8 n)
    (indices : List Usize) (coefficients : Coefficients)
    (bound : ∀ i∈indices,i.val<n.val)
    (values : ∀ i∈indices,∃ exponent,Array.index_usize exponents i=ok exponent ∧ exponent.val<27) :
    ∃ out,PV_B3_Range117.scatter input exponents indices coefficients=ok out := by
  induction indices generalizing coefficients with
  | nil => exact ⟨coefficients,rfl⟩
  | cons i rest ih =>
    obtain ⟨q,hq⟩ := ProverRwP6ArrayRead.read input i (bound i (by simp))
    have coord : (i &&& 3#usize).val<4 := by
      change (i &&& 3#usize).bv.toNat<4
      rw [UScalar.bv_and,BitVec.toNat_and]
      exact lt_of_le_of_lt Nat.and_le_right (by decide)
    obtain ⟨value,hv⟩ := PV_RunJoin_MaskPreparedTotal69.tower q (i &&& 3#usize) coord
    obtain ⟨exponent,he,hsmall⟩ := values i (by simp)
    have cast : (UScalar.cast .Usize exponent).val<27 := by scalar_tac
    obtain ⟨next,update,hvalue⟩ := WP.spec_imp_exists
      (Array.update_spec coefficients (UScalar.cast .Usize exponent) value
        (by simpa only [Array.length,coefficients.property] using cast))
    obtain ⟨out,ho⟩ := ih next
      (fun j hj => bound j (by simp only [List.mem_cons];exact Or.inr hj))
      (fun j hj => values j (by simp only [List.mem_cons];exact Or.inr hj))
    exact ⟨out,by simp only [PV_B3_Range117.scatter,lift,hq,hv,he,update,ho,bind_tc_ok]⟩

theorem horner (coefficients : Coefficients) (prepared : host_arithmetic.PreparedQm31Multiplier)
    (indices : List Usize) (shared : Q) (bound : ∀ i∈indices,i.val<27) :
    ∃ out,PV_B3_Range117.horner coefficients prepared indices shared=ok out := by
  induction indices generalizing shared with
  | nil => exact ⟨shared,rfl⟩
  | cons i rest ih =>
    obtain ⟨product,hp⟩ := PV_RunJoin_MaskPreparedTotal69.mul prepared shared
    obtain ⟨q,hq⟩ := ProverRwP6ArrayRead.read coefficients i (bound i (by simp))
    obtain ⟨next,hn⟩ := qadd product q
    obtain ⟨out,ho⟩ := ih next (fun j hj => bound j (by simp only [List.mem_cons];exact Or.inr hj))
    exact ⟨out,by simp only [PV_B3_Range117.horner,hp,hq,hn,ho,bind_tc_ok]⟩

#print axioms scatter
#print axioms horner
end R1Z.PV_RunJoin_MaskRangeTotal69
