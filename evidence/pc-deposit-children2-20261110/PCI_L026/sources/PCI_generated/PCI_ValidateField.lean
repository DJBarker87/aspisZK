import PCI_ValidateCarrier
import PCI_Mul
import PCC_PairValidation
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace PCI_ValidateField
open PCI_ValidateWords PCI_ValidateCarrier
/-- The actual CLOSED emitted field call, at the exact prepared operands. -/
def mul_run (a b : UInt32) : Result UInt32 := do
  let z ← AspisR1SemanticCallExtraction.aspis_core.field.M31.mul (word a) (word b)
  ok (readWord z)

theorem mul_result (a b : UInt32) : mul_run a b=ok (PCC.fieldMul a b) := by
  obtain ⟨z,hz,hvalue,_⟩ := PCI_Mul.value (word a) (word b)
  simp only [word_value] at hvalue
  unfold mul_run
  rw [hz]
  simp only [bind_tc_ok]
  change ok (UInt32.ofNat z.val)=ok (UInt32.ofNat ((a.toNat*b.toNat)%2147483647))
  rw [hvalue]

theorem mul_canonical (a b : UInt32) : (PCC.fieldMul a b).toNat<2147483647 := by
  have hm : (a.toNat*b.toNat)%2147483647<2147483647 := Nat.mod_lt _ (by decide)
  have hb : (a.toNat*b.toNat)%2147483647<4294967296 := by omega
  unfold PCC.fieldMul
  rw [UInt32.toNat_ofNat_of_lt' hb]
  exact hm

theorem sub_canonical (a b : UInt32) : (PCC.fieldSub a b).toNat<2147483647 := by
  have hm : (a.toNat+2147483647-b.toNat)%2147483647<2147483647 := Nat.mod_lt _ (by decide)
  have hb : (a.toNat+2147483647-b.toNat)%2147483647<4294967296 := by omega
  unfold PCC.fieldSub
  rw [UInt32.toNat_ofNat_of_lt' hb]
  exact hm

/-- Same-word, exact Result and canonical value for each model operation.
    Canonical caller domains are proved separately from the entered gates. -/
theorem same_call (a b : UInt32) :
    ∃ z, AspisR1SemanticCallExtraction.aspis_core.field.M31.mul (word a) (word b)=ok z ∧
      readWord z=PCC.fieldMul a b ∧ z.val<2147483647 := by
  obtain ⟨z,hz,hvalue,hcanonical⟩ := PCI_Mul.value (word a) (word b)
  refine ⟨z,hz,?_,hcanonical⟩
  change UInt32.ofNat z.val=UInt32.ofNat ((a.toNat*b.toNat)%2147483647)
  apply congrArg UInt32.ofNat
  simpa only [word_value] using hvalue

#print axioms mul_result
#print axioms mul_canonical
#print axioms sub_canonical
#print axioms same_call
end PCI_ValidateField
