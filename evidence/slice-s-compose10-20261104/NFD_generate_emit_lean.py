from pathlib import Path
E=Path(__file__).resolve().parent
s='''import NEY_EmitComposed
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
'''
fields=['master_account','selected_lane_account','output_lane','nullifier','verified_afterstate.next_pair_index','verified_afterstate.next_root','verified_afterstate.next_frontier']
for n,f in enumerate(fields,1):
 s+=f'  have h{n} : a.{f}=b.{f} := by\n'
 if n in [1,2,4,6,7]:
  s+='    apply NED_WindowExtensionality.array_ext\n'
  index='k' if n==7 else 'j' if n in [1,2] else 'i'
  s+=f'    intro {index}\n'
  if n==7:s+='    apply NED_WindowExtensionality.array_ext\n    intro i\n'
 s+='    apply UScalar.eq_of_val_eq\n'
 s+=f'    exact point ⟨{n},by decide⟩ '+('i' if n in [4,6,7] else '⟨0,by decide⟩')+' '+('j' if n in [1,2] else '⟨0,by decide⟩')+' '+('k' if n==7 else '⟨0,by decide⟩')+'\n'
s+='''  cases a with
  | mk ak am asl al an aa =>
    cases aa
    cases b with
    | mk bk bm bsl bl bn ba =>
      cases ba
      simp_all only

'''
values=['kindCode (AspisR1.S2K.ResultAdmission.kind s)','(get (AspisR1.S2K.StatementAdmission.common s).master_account j).val','(get (AspisR1.S2K.StatementAdmission.common s).selected_lane_account j).val','(AspisR1.S2K.StatementAdmission.common s).output_lane.val','(get (AspisR1.S2K.StatementChecks.nullifier s) i).val','(AspisR1.S2K.StatementAdmission.common s).lane_transition.candidate_afterstate.next_pair_index.val','(get (AspisR1.S2K.StatementAdmission.common s).lane_transition.candidate_afterstate.next_root i).val','(get (get (AspisR1.S2K.StatementAdmission.common s).lane_transition.candidate_afterstate.next_frontier k) i).val']
for n,value in enumerate(values):
 s+=f'theorem alignment{n} (s : Statement) (i : Fin 8) (j : Fin 32) (k : Fin 20) :\n    project (derived s) ⟨{n},by decide⟩ i j k = {value} := rfl\n'
s+='\n#print axioms complete\n'+''.join(f'#print axioms alignment{n}\n' for n in range(8))+'end NFD_EmitProjection\n'
(E/'NFD_EmitProjection.lean').write_text(s)
