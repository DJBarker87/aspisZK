import R1Z.PV_RunJoin_CheckBaseLength60
import R1Z.PV_RunJoin_BackendMRows58
import R1Z.PV_RunJoin_ResultPost
import R1Z.ProverRw19LoopBind
set_option autoImplicit false
namespace R1Z.PV_RunJoin_CheckColumnsLength66
open Aeneas Aeneas.Std Result ProverRwFull
open PV_RunJoin_BackendMRows58 (Columns column)
variable [ExternalTypes] [ExternalFuns]

def Status (columns : Columns) (start : Nat)
    (result : Option (core.result.Result Unit r1_wire.Error)) : Prop :=
  match result with
  | some (.Err _) => True
  | _ => ∀ l,start≤l → l<26 → (column columns l).length=1024

theorem loop (columns : Columns) (n : Nat) (lane : Usize) (rank : lane.val+n=26)
    (result : Option (core.result.Result Unit r1_wire.Error))
    (success : host_semantic.check_base_columns_loop columns lane=ok result) :
    Status columns lane.val result := by
  induction n generalizing lane result with
  | zero =>
    have stop : ¬lane<26#usize := by change ¬lane.val<26;omega
    unfold host_semantic.check_base_columns_loop at success
    rw [ProverRw19LoopBind.loop_bind] at success
    simp only [host_semantic.check_base_columns_loop.body,stop,if_false,bind_tc_ok] at success
    cases Result.ok.inj success
    intro l lower upper
    omega
  | succ n ih =>
    have more : lane<26#usize := by change lane.val<26;omega
    have next : (Usize.wrapping_add lane 1#usize).val=lane.val+1 :=
      PV_RunJoin_CompactStep39.offset lane 1#usize (by have h : 26≤Usize.max := by scalar_tac;omega)
    have hc : Array.index_usize columns lane=ok (column columns lane.val) := by
      rw [ProverCommitArrayIndex25.array_index_usize_ok columns lane more]
      simp only [column,Nat.mod_eq_of_lt more]
    unfold host_semantic.check_base_columns_loop at success
    rw [ProverRw19LoopBind.loop_bind] at success
    simp only [host_semantic.check_base_columns_loop.body,more,if_true,hc,bind_tc_ok] at success
    obtain ⟨checked,hchecked,success⟩ := PV_RunJoin_ResultPost.bind_eq_ok success
    cases checked with
    | Err e =>
      simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok,
        core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
        core.convert.FromSame] at success
      cases Result.ok.inj success
      trivial
    | Ok unit =>
      cases unit
      have len := PV_RunJoin_CheckBaseLength60.complete (alloc.vec.Vec.deref (column columns lane.val)) hchecked
      simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok,lift] at success
      have tail := ih (Usize.wrapping_add lane 1#usize) (by rw [next];omega) result success
      have extend : (∀ l,lane.val+1≤l → l<26 → (column columns l).length=1024) →
          ∀ l,lane.val≤l → l<26 → (column columns l).length=1024 := by
        intro ht l lower upper
        by_cases eq : l=lane.val
        · subst l;exact len
        · exact ht l (by omega) upper
      cases result with
      | none => exact extend (by simpa only [Status,next] using tail)
      | some r => cases r with
        | Err e => trivial
        | Ok unit => exact extend (by simpa only [Status,next] using tail)

theorem complete (columns : Columns)
    (success : host_semantic.check_base_columns columns=ok (.Ok ())) :
    ∀ l,l<26 → (column columns l).length=1024 := by
  unfold host_semantic.check_base_columns at success
  obtain ⟨result,hr,success⟩ := PV_RunJoin_ResultPost.bind_eq_ok success
  have h := loop columns 26 0#usize rfl result hr
  cases result with
  | none => exact fun l hl => h l (Nat.zero_le l) hl
  | some r =>
    cases r with
    | Err e => cases success
    | Ok unit => exact fun l hl => h l (Nat.zero_le l) hl

#print axioms Status
#print axioms loop
#print axioms complete
end R1Z.PV_RunJoin_CheckColumnsLength66
