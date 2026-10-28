import PV_B3P_BytesV3Emission226
namespace PV_B3P_ProjectV3Law226
open Aeneas Aeneas.Std PV_B3P_226V3
set_option autoImplicit false

def value (p : reference226.Source) : reference226.OwnedPublic :=
  match p with
  | .Transfer pub t =>
    {withdrawal := false, anchor := pub.anchor_root, nullifier := pub.nullifier,
     asset_id := pub.asset_id, recipient := pub.recipient_commitment,
     change := pub.change_commitment, withdrawal_amount := 0#u32,
     next_pair_index := t.live_snapshot.next_pair_index,
     frontier := t.live_snapshot.frontier, next_root := t.candidate_afterstate.next_root,
     next_frontier := t.candidate_afterstate.next_frontier}
  | .Withdrawal pub t =>
    {withdrawal := true, anchor := pub.anchor_root, nullifier := pub.nullifier,
     asset_id := pub.asset_id, recipient := Array.repeat 8#usize aspis_core.field.M31.ZERO,
     change := pub.change_commitment, withdrawal_amount := pub.amount,
     next_pair_index := t.live_snapshot.next_pair_index,
     frontier := t.live_snapshot.frontier, next_root := t.candidate_afterstate.next_root,
     next_frontier := t.candidate_afterstate.next_frontier}

theorem project_exact (p : reference226.Source) :
    reference226.project p = .ok (value p) := by cases p <;> rfl

theorem project_success (p : reference226.Source) :
    ∃ out, reference226.project p = .ok out := ⟨value p,project_exact p⟩

theorem complete_source (p : reference226.Source) :
    reference226.public_bytes p = reference226.encode_owned (value p) := by
  simp only [reference226.public_bytes,project_exact,bind_tc_ok]

#print axioms project_exact
#print axioms project_success
#print axioms complete_source
end PV_B3P_ProjectV3Law226
