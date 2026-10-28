import NDO_JGf_TX2_M0Level17
import RPt_JFo_Prepared
import Port4B_KeyInstall
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGf_TX2_M0Root
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open OracleDecisionMultiBuild OracleDecisionMultiTree JGf_TX2_M0Roots

def retainedRoot : State := JGc_TX2_HashBytes.state
  [154,186,129,123,118,141,34,107,41,162,65,31,231,186,247,183,
   176,78,206,66,178,115,221,182,126,10,44,98,98,19,142,75]

theorem selected_queries : OraclePortSelectedDraft.selected
    (Port4B_KeyInstall.queries JFo_Prepared.value.queries) 1 0=indices := rfl
#print axioms selected_queries

theorem selected_root :
    (AspisV8R19.SqueezeOracleBridge.encodeState retainedRoot).val=JFq_Root0.value.val := by rfl
#print axioms selected_root

theorem saved_root : (JFx_NativeBytes.checkpoint.val.drop 112).take 32=
    (AspisV8R19.SqueezeOracleBridge.encodeState retainedRoot).val :=
  JFq_Root0.selected.trans selected_root.symm
#print axioms saved_root

theorem value_eq : value185=retainedRoot := by
  funext i
  fin_cases i <;> rfl
#print axioms value_eq

theorem source (f : Nat → Bytes) (g : Nat → Nat → State)
    (inputs : InputLaw f) (siblings : SiblingLaw g) :
    root JFp_SHADigest.digest (build indices f g 18 0)=retainedRoot := by
  rw [shape185 f g inputs siblings,root185,value_eq]
#print axioms source

theorem inhabited : ∃ (f : Nat → Bytes) (g : Nat → Nat → State),
    InputLaw f ∧ SiblingLaw g ∧
    root JFp_SHADigest.digest (build indices f g 18 0)=retainedRoot :=
  ⟨inputAt,siblingAt,(by intro b _;rfl),(by intro h _ b _;rfl),
    source inputAt siblingAt (by intro b _;rfl) (by intro h _ b _;rfl)⟩
#print axioms inhabited
end AspisR1.JGf_TX2_M0Root
end
