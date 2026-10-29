import PV_B3P_PreweightedLoop12227
import PV_B3P_SumOperation11227
import PV_B3P_EqualityBinding9227
import PV_B3P_ReconstructBinding9227
import PV_B3P_CopyActiveLoop12227
import PV_B3P_LeadingBinding12227
import PV_B3P_DigestStore11227
import PV_B3P_RoundQPlain11227
import PV_B3P_RoundQPacked11227
import PV_B3P_RoundMPlain11227
import PV_B3P_RoundMPacked11227
namespace PV_B3P_Binding12227
open Aeneas Aeneas.Std PV_B3P_227 PV_B3P_Binding11227 PV_B3P_Binding10227
set_option autoImplicit false

def source_active12 (selectors : reference_copy_terminal.Selectors) : Result aspis_core.field.QM31 :=
  PV_B3P_Ordered227.fold (active_step12 selectors) (usize_indices11 64 0#usize) aspis_core.field.QM31.ZERO
theorem active_operation12 : reference_copy_terminal.Selectors.active = source_active12 :=
  funext active_literal_fold12

def source_leading12 (openings : aspis_statement.state_only_poseidon.StateOnlyPoseidonOpenings) :
    Result (Array aspis_core.field.QM31 4#usize) :=
  PV_B3P_Ordered227.fold (leading_step12 openings.xor12_z)
    [0#usize,1#usize,2#usize,3#usize,4#usize,5#usize,6#usize,7#usize] openings.z >>= leading_finish12
theorem leading_operation12 : reference_poseidon.leading_pair_packed = source_leading12 :=
  funext leading_pair_packed_binding12

def source_digest_store12 (output : Array aspis_core.field.QM31 8#usize)
    (selector : aspis_core.field.QM31) (opened : Array aspis_core.field.QM31 16#usize)
    (start : Usize) (expected : Array aspis_core.field.M31 8#usize) (right_tweak : Bool) :
    Result (Array aspis_core.field.QM31 8#usize) :=
  PV_B3P_Ordered227.fold (digest_store_cell11 selector opened start expected right_tweak)
    [0#usize,1#usize,2#usize,3#usize,4#usize,5#usize,6#usize,7#usize] output
theorem digest_store_operation12 : reference_terminal.add_digest_binding = source_digest_store12 := by
  funext output selector opened start expected right_tweak
  exact digest_store_fold11 output selector opened start expected right_tweak

#print axioms active_operation12
#print axioms leading_operation12
#print axioms digest_store_operation12
end PV_B3P_Binding12227
