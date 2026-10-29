import PV_B3P_SemanticCallersSuccess227
import PV_B3P_CarrySuccess227
import PV_B3P_PublicSuccess227
namespace PV_B3P_Success227
open Aeneas Aeneas.Std PV_B3P_227
set_option autoImplicit false
abbrev Digest8Q := Array aspis_core.field.QM31 8#usize

theorem digest_field_anchor (p : reference_terminal.SemanticPublic) :
    (valid_public p).anchor = p.anchor := rfl
#print axioms digest_field_anchor

theorem digest_field_nullifier (p : reference_terminal.SemanticPublic) :
    (valid_public p).nullifier = p.nullifier := rfl
#print axioms digest_field_nullifier

theorem digest_field_recipient (p : reference_terminal.SemanticPublic) :
    (valid_public p).recipient = p.recipient := rfl
#print axioms digest_field_recipient

theorem digest_field_change (p : reference_terminal.SemanticPublic) :
    (valid_public p).change = p.change := rfl
#print axioms digest_field_change

theorem digest_field_index (p : reference_terminal.SemanticPublic) :
    (valid_public p).transition.live_snapshot.next_pair_index = 0#u64 := rfl
#print axioms digest_field_index

theorem digest_field_frontier (p : reference_terminal.SemanticPublic) :
    (valid_public p).transition.live_snapshot.frontier = empty_frontier := rfl
#print axioms digest_field_frontier

theorem digest_field_next_root (p : reference_terminal.SemanticPublic) :
    (valid_public p).transition.candidate_afterstate.next_root = p.transition.candidate_afterstate.next_root := rfl
#print axioms digest_field_next_root

theorem digest_field_next_frontier (p : reference_terminal.SemanticPublic) :
    (valid_public p).transition.candidate_afterstate.next_frontier = empty_frontier := rfl
#print axioms digest_field_next_frontier

theorem digest_field_opened (o : aspis_statement.state_only_poseidon.StateOnlyPoseidonOpenings) :
    o.z = o.z := rfl
#print axioms digest_field_opened
end PV_B3P_Success227
