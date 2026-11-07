import NMX_R2_ErrorInverse
set_option autoImplicit false
namespace NMX_R2_ErrorModelInverse
open Aeneas Aeneas.Std AdapterRw NMX_R2_Carrier

theorem word (w : UInt32) : NMX_R2_Carrier.word (NMX_R2_ErrorInverse.fromWord w) = w := by
 simp [NMX_R2_Carrier.word,NMX_R2_ErrorInverse.fromWord,UScalar.ofNatCore_val_eq]

theorem error (e : RSL.ProgramError) :
 NMX_R2_Carrier.error (NMX_R2_ErrorInverse.fromError e) = e := by
 cases e <;> simp only [NMX_R2_ErrorInverse.fromError,NMX_R2_Carrier.error,word]
#print axioms word
#print axioms error
end NMX_R2_ErrorModelInverse
