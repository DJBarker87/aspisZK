import NEU_PublicProjections
set_option autoImplicit false
namespace NEU_CommonProjections
open Aeneas Aeneas.Std
open NEU_PublicProjections (get)
abbrev Common := AspisR1AdapterReconstruct.aspis_statement.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalCommonV1

def value (c : Common) (slot : Fin 15) (i : Fin 8) (j : Fin 32) (k : Fin 20) : Nat :=
  match slot.val with
  | 0 => (get c.master_account j).val
  | 1 => (get c.checkpoint_account j).val
  | 2 => (get c.selected_lane_account j).val
  | 3 => c.output_lane.val
  | 4 => c.checkpoint_sequence.val
  | 5 => (get c.historical_global_anchor i).val
  | 6 => (get c.lane_transition.live_snapshot.pool j).val
  | 7 => (get c.lane_transition.live_snapshot.deployment_domain j).val
  | 8 => c.lane_transition.live_snapshot.sequence.val
  | 9 => c.lane_transition.live_snapshot.next_pair_index.val
  | 10 => (get c.lane_transition.live_snapshot.current_root i).val
  | 11 => (get (get c.lane_transition.live_snapshot.frontier k) i).val
  | 12 => c.lane_transition.candidate_afterstate.next_pair_index.val
  | 13 => (get c.lane_transition.candidate_afterstate.next_root i).val
  | _ => (get (get c.lane_transition.candidate_afterstate.next_frontier k) i).val

/-- One arbitrary field/byte/word/frontier projection identifies the complete
nested common record. No unread positions are fixed to fixture values. -/
theorem common_ext (c d : Common)
    (point : ∀ slot i j k, value c slot i j k=value d slot i j k) : c=d := by
  have h0 : c.master_account=d.master_account := by
    apply NED_WindowExtensionality.array_ext
    intro j
    apply UScalar.eq_of_val_eq
    exact point ⟨0,by decide⟩ ⟨0,by decide⟩ j ⟨0,by decide⟩
  have h1 : c.checkpoint_account=d.checkpoint_account := by
    apply NED_WindowExtensionality.array_ext
    intro j
    apply UScalar.eq_of_val_eq
    exact point ⟨1,by decide⟩ ⟨0,by decide⟩ j ⟨0,by decide⟩
  have h2 : c.selected_lane_account=d.selected_lane_account := by
    apply NED_WindowExtensionality.array_ext
    intro j
    apply UScalar.eq_of_val_eq
    exact point ⟨2,by decide⟩ ⟨0,by decide⟩ j ⟨0,by decide⟩
  have h3 : c.output_lane=d.output_lane := by
    apply UScalar.eq_of_val_eq
    exact point ⟨3,by decide⟩ ⟨0,by decide⟩ ⟨0,by decide⟩ ⟨0,by decide⟩
  have h4 : c.checkpoint_sequence=d.checkpoint_sequence := by
    apply UScalar.eq_of_val_eq
    exact point ⟨4,by decide⟩ ⟨0,by decide⟩ ⟨0,by decide⟩ ⟨0,by decide⟩
  have h5 : c.historical_global_anchor=d.historical_global_anchor := by
    apply NED_WindowExtensionality.array_ext
    intro i
    apply UScalar.eq_of_val_eq
    exact point ⟨5,by decide⟩ i ⟨0,by decide⟩ ⟨0,by decide⟩
  have h6 : c.lane_transition.live_snapshot.pool=d.lane_transition.live_snapshot.pool := by
    apply NED_WindowExtensionality.array_ext
    intro j
    apply UScalar.eq_of_val_eq
    exact point ⟨6,by decide⟩ ⟨0,by decide⟩ j ⟨0,by decide⟩
  have h7 : c.lane_transition.live_snapshot.deployment_domain=d.lane_transition.live_snapshot.deployment_domain := by
    apply NED_WindowExtensionality.array_ext
    intro j
    apply UScalar.eq_of_val_eq
    exact point ⟨7,by decide⟩ ⟨0,by decide⟩ j ⟨0,by decide⟩
  have h8 : c.lane_transition.live_snapshot.sequence=d.lane_transition.live_snapshot.sequence := by
    apply UScalar.eq_of_val_eq
    exact point ⟨8,by decide⟩ ⟨0,by decide⟩ ⟨0,by decide⟩ ⟨0,by decide⟩
  have h9 : c.lane_transition.live_snapshot.next_pair_index=d.lane_transition.live_snapshot.next_pair_index := by
    apply UScalar.eq_of_val_eq
    exact point ⟨9,by decide⟩ ⟨0,by decide⟩ ⟨0,by decide⟩ ⟨0,by decide⟩
  have h10 : c.lane_transition.live_snapshot.current_root=d.lane_transition.live_snapshot.current_root := by
    apply NED_WindowExtensionality.array_ext
    intro i
    apply UScalar.eq_of_val_eq
    exact point ⟨10,by decide⟩ i ⟨0,by decide⟩ ⟨0,by decide⟩
  have h11 : c.lane_transition.live_snapshot.frontier=d.lane_transition.live_snapshot.frontier := by
    apply NED_WindowExtensionality.array_ext
    intro k
    apply NED_WindowExtensionality.array_ext
    intro i
    apply UScalar.eq_of_val_eq
    exact point ⟨11,by decide⟩ i ⟨0,by decide⟩ k
  have h12 : c.lane_transition.candidate_afterstate.next_pair_index=d.lane_transition.candidate_afterstate.next_pair_index := by
    apply UScalar.eq_of_val_eq
    exact point ⟨12,by decide⟩ ⟨0,by decide⟩ ⟨0,by decide⟩ ⟨0,by decide⟩
  have h13 : c.lane_transition.candidate_afterstate.next_root=d.lane_transition.candidate_afterstate.next_root := by
    apply NED_WindowExtensionality.array_ext
    intro i
    apply UScalar.eq_of_val_eq
    exact point ⟨13,by decide⟩ i ⟨0,by decide⟩ ⟨0,by decide⟩
  have h14 : c.lane_transition.candidate_afterstate.next_frontier=d.lane_transition.candidate_afterstate.next_frontier := by
    apply NED_WindowExtensionality.array_ext
    intro k
    apply NED_WindowExtensionality.array_ext
    intro i
    apply UScalar.eq_of_val_eq
    exact point ⟨14,by decide⟩ i ⟨0,by decide⟩ k
  cases c with
  | mk m0 ch0 sl0 l0 seq0 an0 lt0 =>
    cases lt0 with
    | mk live0 candidate0 =>
      cases live0
      cases candidate0
      cases d with
      | mk m1 ch1 sl1 l1 seq1 an1 lt1 =>
        cases lt1 with
        | mk live1 candidate1 =>
          cases live1
          cases candidate1
          simp_all only

#print axioms common_ext
end NEU_CommonProjections
