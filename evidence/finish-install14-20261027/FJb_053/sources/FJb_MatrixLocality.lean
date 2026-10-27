import FJb_MatrixModel
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJb_MatrixLocality
open FIv_NativeValue (K)
open FJb_MatrixModel (Values sample block)
/-- Distinct source groups cannot overwrite another group's lane. -/
theorem outside (v : Values) (g : Nat) (j : Fin (16#usize).val)
    (hne : j.val/4≠g) : block v g j=v j := by
  have h0 : j.val≠4*g := by intro e;apply hne;omega
  have h1 : j.val≠4*g+1 := by intro e;apply hne;omega
  have h2 : j.val≠4*g+2 := by intro e;apply hne;omega
  have h3 : j.val≠4*g+3 := by intro e;apply hne;omega
  simp only [block,if_neg h0,if_neg h1,if_neg h2,if_neg h3]

theorem sample_other (v : Values) (g h : Nat) (hh : h < 4) (hne : h≠g)
    (k : Fin (4#usize).val) :
    sample (block v g) (4*h+k.val)=sample v (4*h+k.val) := by
  have hk : k.val < 4 := k.isLt
  have hb : 4*h+k.val < (16#usize).val := by change 4*h+k.val < 16;omega
  simp only [sample,dif_pos hb]
  apply outside
  change (4*h+k.val)/4≠g
  omega

theorem sample_same (v : Values) (g : Nat) (hg : g < 4)
    (k : Fin (4#usize).val) :
    sample (block v g) (4*g+k.val)=R0P.poseidonMat4
      (fun j=>sample v (4*g+j.val)) k := by
  have hk : k.val < 4 := k.isLt
  have hb : 4*g+k.val < (16#usize).val := by change 4*g+k.val < 16;omega
  simp only [sample,dif_pos hb,block]
  fin_cases k <;> simp
#print axioms outside
#print axioms sample_other
#print axioms sample_same
end AspisR1.FJb_MatrixLocality
end
