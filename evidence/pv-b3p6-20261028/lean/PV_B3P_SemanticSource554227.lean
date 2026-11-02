import PV_B3P_Caller1204227
import PV_B3P_NativePreweighted15227
import PV_B3P_LinkDefinitions13227
namespace PV_B3P_Association554227
open Aeneas Aeneas.Std PV_B3P_227 PV_B3P_Native15227 PV_B3P_Binding12227
set_option autoImplicit false

def semantic_source554 := context12_preweighted_reference_terminal_semantic_packed (@native_preweighted15)

theorem semantic_source_reference554 (public1 : reference_terminal.SemanticPublic)
    (openings : aspis_statement.state_only_poseidon.StateOnlyPoseidonOpenings)
    (selectors : reference_copy_terminal.Selectors) :
    semantic_source554 public1 openings selectors = reference_terminal.semantic_packed public1 openings selectors := by
  unfold semantic_source554
  rw [native_preweighted_binding15]
  unfold context12_preweighted_reference_terminal_semantic_packed reference_terminal.semantic_packed
  rfl

theorem semantic_source_link554 :
    PV_B3P_Links13227.PV_B3P_Link_terminal_semantic_packed semantic_source554 :=
  funext fun p => funext fun openings => funext (semantic_source_reference554 p openings)

#print axioms semantic_source_reference554
#print axioms semantic_source_link554
end PV_B3P_Association554227
