import RPu_FJc_InactiveCoefficientsValue
import RPu_FJc_InactiveContractValue
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJc_InactiveValue
open Aeneas Aeneas.Std Result AspisR1CurrentWide.Proof
open FIo_FieldBridge (NE wide)

def sumPrefix (f : Slice U8) (low : Array NE 16#usize) : Nat → AspisWideTower.WideExact
  | 0 => 0
  | n+1 => sumPrefix f low n + FJc_InactiveCoefficientsModel.sumPrefix f n 64 *
      FJc_SubsetModel.sumPrefix low n 16

theorem replace (f : Slice U8) (low : Array NE 16#usize) (cs : Array NE 12#usize)
    (hc : ∀ g,FIp_ArrayValue.value cs g=FJc_InactiveCoefficientsModel.sumPrefix f g 64)
    (n : Nat) : FJc_InactiveContract.sumPrefix low cs n=sumPrefix f low n := by
  induction n with
  | zero => rfl
  | succ n ih => rw [FJc_InactiveContract.sumPrefix,sumPrefix,ih,hc]

/-- Complete native grouped inactive contraction VALUE on the original f/low.
Its mathematical table-to-inactive-row interpretation is a separate join. -/
theorem value (f : Slice U8) (low : Array NE 16#usize) (out : NE)
    (hlow : FIo_ArrayCanon.Holds low)
    (run : FIo_Native.weights.s2_grouped_inactive_pair f low=ok out) :
    FIo_WideValues.Canon out ∧ decodeWide (wide out)=sumPrefix f low 12 := by
  unfold FIo_Native.weights.s2_grouped_inactive_pair at run
  obtain ⟨cs,hcs,run⟩ := Port3_PushFrame.bind_success _ _ _ run
  have csValue := FJc_InactiveCoefficientsValue.sixtyfour f cs hcs
  have outValue := FJc_InactiveContractValue.twelve low cs hlow csValue.1 out run
  exact ⟨outValue.1,outValue.2.trans (replace f low cs csValue.2 12)⟩
#print axioms replace
#print axioms value
end AspisR1.FJc_InactiveValue
end
