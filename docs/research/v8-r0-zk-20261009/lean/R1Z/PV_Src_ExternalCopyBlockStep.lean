import R1Z.PV_Src_ExternalBlockStep

/-! The modulo-copy block reads the fixed original state and writes the same
four cells as the owned source block. -/
set_option autoImplicit false
namespace R1Z.PV_Src_ExternalCopyBlockStep
open Aeneas Aeneas.Std Result R0Z.WriterRefine
open PV_Src_ExternalBlockStep

theorem mul_comm (g : Usize) (hg : g.val < 4) :
    Usize.wrapping_mul 4#usize g = base g := by
  apply UScalar.eq_of_val_eq
  rw [umul _ _ (by simp;omega),base_val g hg]
  rfl

theorem source (s out : State) (g : Usize) (hg : g.val < 4)
    (m : Array U32 4#usize)
    (hm : R0PoseidonCopy.mat4 s.val[(base g).val]!
      s.val[(Usize.wrapping_add (base g) 1#usize).val]!
      s.val[(Usize.wrapping_add (base g) 2#usize).val]!
      s.val[(Usize.wrapping_add (base g) 3#usize).val]! = ok m) :
    R0PoseidonCopy.ext_groups_loop s out g =
      R0PoseidonCopy.ext_groups_loop s (write out g m)
        (Usize.wrapping_add g 1#usize) := by
  have b0 : (base g).val < (16#usize : Usize).val := by rw [base_val g hg];simp;omega
  have b1 : (Usize.wrapping_add (base g) 1#usize).val < (16#usize : Usize).val := by
    rw [offset_val g hg _ (by decide)];simp;omega
  have b2 : (Usize.wrapping_add (base g) 2#usize).val < (16#usize : Usize).val := by
    rw [offset_val g hg _ (by decide)];simp;omega
  have b3 : (Usize.wrapping_add (base g) 3#usize).val < (16#usize : Usize).val := by
    rw [offset_val g hg _ (by decide)];simp;omega
  rw [R0PoseidonCopy.ext_groups_loop,if_pos (by simpa [UScalar.lt_equiv] using hg)]
  simp only [mul_comm g hg,lift,bind_tc_ok,index_ok s _ b0,index_ok s _ b1,
    index_ok s _ b2,index_ok s _ b3,hm,index_ok m 0#usize (by decide),
    index_ok m 1#usize (by decide),index_ok m 2#usize (by decide),
    index_ok m 3#usize (by decide),update_ok _ _ _ b0,update_ok _ _ _ b1,
    update_ok _ _ _ b2,update_ok _ _ _ b3,write,UScalar.ofNatCore_val_eq]

#print axioms mul_comm
#print axioms source
end R1Z.PV_Src_ExternalCopyBlockStep
