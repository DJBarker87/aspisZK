import NDO_JGd_MaskedGate
set_option autoImplicit false
namespace AspisR1.JGe_Gate
open Aeneas Aeneas.Std Result JGd_NumericData

theorem continuation {α : Type} (k : FIp_SemanticArithmetic.MQ → Result α) :
    (do let weighted ← FIp_SemanticArithmetic.mul JFm_Begin.challenges.eta neededTerminal
        let sum ← FIp_SemanticArithmetic.add mask weighted
        let q ← Array.index_usize JFu_ClaimsData.a3 28#usize
        let masked ← FIp_SemanticArithmetic.add sum q
        k masked)=k running := by
  have h := congrArg (fun call => do let q ← call; k q) JGd_MaskedGate.source
  simpa only [JGb_MaskedArithmetic.run,bind_assoc_eq,bind_tc_ok] using h
#print axioms continuation
end AspisR1.JGe_Gate
