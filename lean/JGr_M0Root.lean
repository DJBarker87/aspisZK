import JGr_M0BranchHi
import JGf_TX2_M0Root
import JGe_View
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGr_M0Root
open Aeneas Aeneas.Std
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open OracleDecisionMultiBuild OracleDecisionMultiTree JGr_M0Roots

def retainedRoot : State := JGf_TX2_M0Root.retainedRoot

theorem value_eq : value156=retainedRoot := by
  funext i
  fin_cases i <;> rfl
#print axioms value_eq

theorem source (f : Nat → Bytes) (g : Nat → Nat → State)
    (inputs : InputLaw f) (siblings : SiblingLaw g) :
    root JFp_SHADigest.digest (build indices f g 18 0)=retainedRoot := by
  rw [shape156 f g inputs siblings,root156,value_eq]
#print axioms source

theorem selected_queries : OraclePortSelectedDraft.selected
    (Port4B_KeyInstall.queries JFo_Prepared.value.queries) 0 0=indices := rfl
#print axioms selected_queries

theorem inhabited : ∃ (f : Nat → Bytes) (g : Nat → Nat → State),
    InputLaw f ∧ SiblingLaw g ∧
    root JFp_SHADigest.digest (build indices f g 18 0)=retainedRoot :=
  ⟨inputAt,siblingAt,(by intro b _;rfl),(by intro h _ b _;rfl),
    source inputAt siblingAt (by intro b _;rfl) (by intro h _ b _;rfl)⟩
#print axioms inhabited
end AspisR1.JGr_M0Root
end
