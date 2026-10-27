import RPt_FJi_Accumulations
import RPt_JFr_TX2_DotLaneTotal
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJi_LaneValue
open Aeneas Aeneas.Std Result
open FJi_Accumulations
open FJf_U64Array (cell)
def word (a : Coefficients) (j : Nat) : U32 := a.val[j]?.getD 0#u32

theorem add (a b c : U64) (run : a+b=ok c) : c.val=a.val+b.val := by
  have h := UScalar.add_equiv a b
  rw [run] at h
  exact h.2.1

theorem mul (a b c : U64) (run : a*b=ok c) : c.val=a.val*b.val := by
  have h := UScalar.mul_equiv a b
  change UScalar.mul a b=ok c at run
  rw [run] at h
  exact h.2.1

/-- Actual checked arithmetic gives natural-number VALUES, with no overflow
or canonicality premise smuggled into the caller. -/
theorem value (c : Coefficients) (a : U32) (s out : Sums) (i : Usize)
    (run : lane c a s i=ok out) (j : Nat) :
    (cell out j).val=if i.val=j then (cell s j).val+(word c j).val*a.val
      else (cell s j).val := by
  unfold lane at run
  obtain ⟨w,hw,run⟩ := Port3_PushFrame.bind_success _ _ _ run
  simp only [lift,bind_tc_ok] at run
  obtain ⟨product,hp,run⟩ := Port3_PushFrame.bind_success _ _ _ run
  obtain ⟨old,ho,run⟩ := Port3_PushFrame.bind_success _ _ _ run
  obtain ⟨total,ht,run⟩ := Port3_PushFrame.bind_success _ _ _ run
  rw [FJf_U64Array.update s out i total run j]
  by_cases eq : i.val=j
  · rw [if_pos eq,if_pos eq,add _ _ _ ht,mul _ _ _ hp,
      JFr_TX2_DotLaneTotal.extend,JFr_TX2_DotLaneTotal.extend]
    have oldvalue := FJf_U64Array.read s i old ho
    have wordvalue : word c i.val=w := by
      simp only [word,FJc_ReadSlot.slot c i w hw,Option.getD_some]
    rw [←eq,oldvalue,wordvalue]
  · rw [if_neg eq,if_neg eq]
#print axioms add
#print axioms mul
#print axioms value
end AspisR1.FJi_LaneValue
end
