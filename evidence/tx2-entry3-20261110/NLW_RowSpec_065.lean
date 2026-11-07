import NLT_CompleteRoot
import NLT_Root
import NLW_Root0
set_option autoImplicit false
noncomputable section
namespace NLW_RowSpec_065
open Aeneas Aeneas.Std AspisR1
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
/-- Old interface is retained ONLY as resolved-window projection support;
NLT-F1 withdrew its abort-coverage closure claim. Never promote it. -/
abbrev ResolvedProjectionSpec (H : Bytes → State) (pub proof ck : Slice U8) : Prop :=
 NLT_Root.RowSpec H pub proof ck
/-- Corrected merged full interface: generic original backend/hash and an
independent C04 stopped-call arm,with NO returned native child reply/suffix. -/
abbrev RowSpec_065 (H : Bytes → State) {X : Type}
 (d : VTop_Stages.aspis_core.digest.Digest32 X) (pub proof ck : Slice U8) (hash : X) : Prop :=
 NLT_CompleteRoot.RowSpec H d pub proof ck hash
/-- Exact own-input Root0 clause, including its codec. -/
theorem root0_same (ck proof : Slice U8) :
 NLW_Root0.Binds ck proof ↔ NLP_InputDomain.Root0 ck proof := Iff.rfl
#print RowSpec_065
#print NLT_CompleteRoot.RowSpec
#print NLT_CompleteRoot.Native
#print NLT_CompleteRoot.Law
#print NLT_CompleteRoot.StoppedLaw
#print root0_same
#print axioms root0_same
end NLW_RowSpec_065
