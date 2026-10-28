import NDO_JFw_Frames
import JFw_Values
set_option autoImplicit false
namespace AspisR1.JFw_Y1
open Aeneas Aeneas.Std Result
open MultiproofConeCanonical OraclePortCompactDraft

def stored : Slice U8 := JFw_Frames.window 7031 464
def initial : Slice U8 := ⟨List.replicate 928 0#u8,by simp only [List.length_replicate];scalar_tac⟩

theorem stored_length : stored.length = 464 := JFw_Frames.window_length 7031 464 (by decide)
theorem initial_length : initial.length = 928 := List.length_replicate

theorem inhabited : ∃ expanded,
    AspisS1ValuesOwnedInstallation.expandValues stored initial = ok (.Ok (),expanded) ∧
    expanded.length = 928 ∧
    bytesOf expanded.val = expand 29 (slice JFz_RowGeometry.wire 7031 464) := by
  obtain ⟨expanded,call,length,bytes⟩ := JFw_Values.success stored initial
    (by rw [stored_length]) (by rw [initial_length,stored_length])
    (by rw [stored_length];scalar_tac)
  refine ⟨expanded,call,length.trans initial_length,?_⟩
  rw [stored_length] at bytes
  exact bytes.trans (congrArg (expand 29) (JFw_Frames.window_bytes 7031 464))

#print axioms stored_length
#print axioms initial_length
#print axioms inhabited
end AspisR1.JFw_Y1
