import NEY_EmitComposed
import NEU_PublicProjections
set_option autoImplicit false
noncomputable section
namespace NFD_EmitProjection
open Aeneas Aeneas.Std
open NEU_EmitModel
open NEU_PublicProjections (get)
def kindCode : AspisR1TerminalDecoder.pool_v1.historical_anchor.PoolV1TransitionKind → Nat
  | .PrivateTransfer => 1 | .Withdrawal => 2

def project (r : Output) (slot : Fin 8) (i : Fin 8) (j : Fin 32) (k : Fin 20) : Nat :=
  match slot.val with
  | 0 => kindCode r.transition_kind
  | 1 => (get r.master_account j).val
  | 2 => (get r.selected_lane_account j).val
  | 3 => r.output_lane.val
  | 4 => (get r.nullifier i).val
  | 5 => r.verified_afterstate.next_pair_index.val
  | 6 => (get r.verified_afterstate.next_root i).val
  | _ => (get (get r.verified_afterstate.next_frontier k) i).val

theorem complete (a b : Output)
    (point : ∀ slot i j k, project a slot i j k=project b slot i j k) : a=b := by
  have h0 : a.transition_kind=b.transition_kind := by
    have h := point ⟨0,by decide⟩ ⟨0,by decide⟩ ⟨0,by decide⟩ ⟨0,by decide⟩
    cases ha : a.transition_kind <;> cases hb : b.transition_kind <;>
      simp_all [project,kindCode]
  have h1 : a.master_account=b.master_account := by
    apply NED_WindowExtensionality.array_ext
    intro j
    apply UScalar.eq_of_val_eq
    exact point ⟨1,by decide⟩ ⟨0,by decide⟩ j ⟨0,by decide⟩
  have h2 : a.selected_lane_account=b.selected_lane_account := by
    apply NED_WindowExtensionality.array_ext
    intro j
    apply UScalar.eq_of_val_eq
    exact point ⟨2,by decide⟩ ⟨0,by decide⟩ j ⟨0,by decide⟩
  have h3 : a.output_lane=b.output_lane := by
    apply UScalar.eq_of_val_eq
    exact point ⟨3,by decide⟩ ⟨0,by decide⟩ ⟨0,by decide⟩ ⟨0,by decide⟩
  have h4 : a.nullifier=b.nullifier := by
    apply NED_WindowExtensionality.array_ext
    intro i
    apply UScalar.eq_of_val_eq
    exact point ⟨4,by decide⟩ i ⟨0,by decide⟩ ⟨0,by decide⟩
  have h5 : a.verified_afterstate.next_pair_index=b.verified_afterstate.next_pair_index := by
    apply UScalar.eq_of_val_eq
    exact point ⟨5,by decide⟩ ⟨0,by decide⟩ ⟨0,by decide⟩ ⟨0,by decide⟩
  have h6 : a.verified_afterstate.next_root=b.verified_afterstate.next_root := by
    apply NED_WindowExtensionality.array_ext
    intro i
    apply UScalar.eq_of_val_eq
    exact point ⟨6,by decide⟩ i ⟨0,by decide⟩ ⟨0,by decide⟩
  have h7 : a.verified_afterstate.next_frontier=b.verified_afterstate.next_frontier := by
    apply NED_WindowExtensionality.array_ext
    intro k
    apply NED_WindowExtensionality.array_ext
    intro i
    apply UScalar.eq_of_val_eq
    exact point ⟨7,by decide⟩ i ⟨0,by decide⟩ k
  cases a with
  | mk ak am asl al an aa =>
    cases aa
    cases b with
    | mk bk bm bsl bl bn ba =>
      cases ba
      simp_all only

theorem alignment0 (s : Statement) (i : Fin 8) (j : Fin 32) (k : Fin 20) :
    project (derived s) ⟨0,by decide⟩ i j k = kindCode (AspisR1.S2K.ResultAdmission.kind s) := rfl
theorem alignment1 (s : Statement) (i : Fin 8) (j : Fin 32) (k : Fin 20) :
    project (derived s) ⟨1,by decide⟩ i j k = (get (AspisR1.S2K.StatementAdmission.common s).master_account j).val := rfl
theorem alignment2 (s : Statement) (i : Fin 8) (j : Fin 32) (k : Fin 20) :
    project (derived s) ⟨2,by decide⟩ i j k = (get (AspisR1.S2K.StatementAdmission.common s).selected_lane_account j).val := rfl
theorem alignment3 (s : Statement) (i : Fin 8) (j : Fin 32) (k : Fin 20) :
    project (derived s) ⟨3,by decide⟩ i j k = (AspisR1.S2K.StatementAdmission.common s).output_lane.val := rfl
theorem alignment4 (s : Statement) (i : Fin 8) (j : Fin 32) (k : Fin 20) :
    project (derived s) ⟨4,by decide⟩ i j k = (get (AspisR1.S2K.StatementChecks.nullifier s) i).val := rfl
theorem alignment5 (s : Statement) (i : Fin 8) (j : Fin 32) (k : Fin 20) :
    project (derived s) ⟨5,by decide⟩ i j k = (AspisR1.S2K.StatementAdmission.common s).lane_transition.candidate_afterstate.next_pair_index.val := rfl
theorem alignment6 (s : Statement) (i : Fin 8) (j : Fin 32) (k : Fin 20) :
    project (derived s) ⟨6,by decide⟩ i j k = (get (AspisR1.S2K.StatementAdmission.common s).lane_transition.candidate_afterstate.next_root i).val := rfl
theorem alignment7 (s : Statement) (i : Fin 8) (j : Fin 32) (k : Fin 20) :
    project (derived s) ⟨7,by decide⟩ i j k = (get (get (AspisR1.S2K.StatementAdmission.common s).lane_transition.candidate_afterstate.next_frontier k) i).val := rfl

#print axioms complete
#print axioms alignment0
#print axioms alignment1
#print axioms alignment2
#print axioms alignment3
#print axioms alignment4
#print axioms alignment5
#print axioms alignment6
#print axioms alignment7
end NFD_EmitProjection
