import NMT_345StepSemanticRead
import NMT_R2_PlainObservation
set_option autoImplicit false
noncomputable section
namespace NMT_R2_345AtSemantic
open Aeneas Aeneas.Std NMT_345

def install (c : Calls) : Calls := {c with c5 := semanticCall}

theorem boundary {W : Type} (c : Calls) (s : TagExpected W) :
 tailSemanticRead (install c) s = tailProofRange (install c) ⟨s,semanticValue s.statement⟩ := by
 rw [stepSemanticRead]
 change (do let pub ← semanticCall s.statement; tailProofRange (install c) ⟨s,pub⟩) = _
 rw [semantic_value]
 rfl
#print axioms boundary
end NMT_R2_345AtSemantic
end
