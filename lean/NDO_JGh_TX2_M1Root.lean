import NDO_JGh_TX2_M1Level17
import RPt_JFo_Prepared
import Port4B_KeyInstall
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGh_TX2_M1Root
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open OracleDecisionMultiBuild OracleDecisionMultiTree JGh_TX2_M1Roots

def retainedRoot : State := JGc_TX2_HashBytes.state
  [187,179,50,81,254,209,90,69,227,132,48,25,66,63,114,62,10,165,82,0,175,83,136,107,86,58,136,54,4,206,252,106]

theorem selected_queries : OraclePortSelectedDraft.selected
    (Port4B_KeyInstall.queries JFo_Prepared.value.queries) 1 1=indices := rfl
#print axioms selected_queries

theorem selected_root :
    (AspisV8R19.SqueezeOracleBridge.encodeState retainedRoot).val=JFq_Root1.value.val := by rfl
#print axioms selected_root

theorem saved_root : (JFx_NativeBytes.checkpoint.val.drop 144).take 32=
    (AspisV8R19.SqueezeOracleBridge.encodeState retainedRoot).val :=
  JFq_Root1.selected.trans selected_root.symm
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
end AspisR1.JGh_TX2_M1Root
end
