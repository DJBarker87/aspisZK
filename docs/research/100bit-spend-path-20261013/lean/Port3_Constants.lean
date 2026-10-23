import Port2_Initial
import CheckpointBytes5Output

set_option autoImplicit false
noncomputable section
namespace AspisR1.Port3_Constants
open Aeneas Aeneas.Std
open Port2_Initial CheckpointBytes4ReaderFields CheckpointBytes5Output

theorem source_zero_k : sourceK 0 = zeroK := by rfl

theorem source_one_k : sourceK 1 = oneK := by rfl

theorem source_zero_e : sourceE 0 = zeroE := by rfl

theorem decode_zero_k : ofK zeroK = 0 := by rw [← source_zero_k,ofK_source]

theorem decode_one_k : ofK oneK = 1 := by rw [← source_one_k,ofK_source]

theorem decode_zero_e : ofE zeroE = 0 := by rw [← source_zero_e,ofE_source]

#print axioms source_zero_k
#print axioms source_one_k
#print axioms source_zero_e
#print axioms decode_zero_k
#print axioms decode_one_k
#print axioms decode_zero_e
end AspisR1.Port3_Constants
end
