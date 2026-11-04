import NEV_DotCarrier
import RPz7_FIo_Install
set_option autoImplicit false
noncomputable section
namespace NEV_DotInputs
open Aeneas Aeneas.Std Result AspisR1 NEV_DotCarrier
abbrev Coefficients := Array NE 29#usize
def Canonical (g : Coefficients) : Prop := ∀ value∈g.val,canonE value
/-- The selected coefficient is the SAME actual bounded read from g; no
independently selected canonical value is supplied to the caller proof. -/
theorem selected (g : Coefficients) (canonical : Canonical g) (index : Usize)
    (inside : index.val<29) (value : NE) (run : Array.index_usize g index=ok value) :
    canonE value := by
  have inRange : index.val<g.val.length := by rw [g.property];exact inside
  obtain ⟨actual,actualRun,point⟩ := WP.spec_imp_exists (Array.index_usize_spec g index inRange)
  have same : actual=value := Result.ok.inj (actualRun.symm.trans run)
  have equality : value=g.val[index.val]'inRange := same.symm.trans point
  apply canonical value
  rw [equality]
  exact List.getElem_mem _
/-- Exact canonical eight-word operand returned by the SAME actual projection. -/
theorem limbs (value : NE) (canonical : canonE value) :
    ∃ words,FIo_Native.aspis_core.field.wide_exact.WideExact.to_limbs value=ok words ∧
      ∀ word∈words.val,word.val<2147483647 := by
  let words : Array U32 8#usize:=Array.make 8#usize
    [value.c0.c0.a,value.c0.c0.b,value.c0.c1.a,value.c0.c1.b,
     value.c1.c0.a,value.c1.c0.b,value.c1.c1.a,value.c1.c1.b]
  refine ⟨words,rfl,?_⟩
  intro word member
  simp only [words,Array.make,List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
    first | exact canonical.1.1.1 | exact canonical.1.1.2 | exact canonical.1.2.1 |
      exact canonical.1.2.2 | exact canonical.2.1.1 | exact canonical.2.1.2 |
      exact canonical.2.2.1 | exact canonical.2.2.2
/-- Every reached tail coefficient index belongs to the SAME29-word array. -/
theorem tail_index (position : Nat) (active : position<3) :
    (if position=0 then 28 else 25+position)<29 := by split_ifs <;> omega
#print axioms selected
#print axioms limbs
#print axioms tail_index
end NEV_DotInputs
end
