import NLT_Root
import NLW_Root0
set_option autoImplicit false
noncomputable section
namespace NLW_RowSpec_065
open Aeneas Aeneas.Std AspisR1
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
/-- Full sibling interface, imported without duplicating its proofs. This
job does NOT use the ungated NLT_Root.root as child credit. Every allocator,
ABI, ownership, nested result, history and invalid-prefix clause remains in
this definition. It replaces the insufficient SourceSpec_065 projection. -/
abbrev RowSpec_065 (H : Bytes → State) (pub proof ck : Slice U8) : Prop :=
 NLT_Root.RowSpec H pub proof ck
/-- Exact own-input Root0 clause, including its codec. -/
theorem root0_same (ck proof : Slice U8) :
 NLW_Root0.Binds ck proof ↔ NLP_InputDomain.Root0 ck proof := Iff.rfl
#print RowSpec_065
#print NLT_Root.RowSpec
#print NLT_Root.CallLaw
#print root0_same
#print axioms root0_same
end NLW_RowSpec_065
