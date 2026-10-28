import PV_L2C_VecRead
import PV_L2C_ReferenceSub
import PV_L2C_NativeFold
import PV_L2C_VecBack
import PV_L2C_VecShape
import PV_L2C_RowEnumeration
set_option autoImplicit false
namespace PV_L2C_ScalarBalance
open Aeneas Aeneas.Std Result AspisR1ProverBalance9
open PV_L2C_M31 PV_L2C_ReferenceArithmetic PV_L2C_NativeFold
open R1Z.ProverCommitFoldSteps R1Z.ProverCommitBalanceRecursion

def lookup (table : Fin 1024 → word) (r : Usize) : word :=
  if h : r.val<1024 then table ⟨r.val,h⟩ else 0

def flag (active : Fin 1024 → Bool) (r : Usize) : Bool :=
  if h : r.val<1024 then active ⟨r.val,h⟩ else true

def selected (table : Fin 1024 → word) (active : Fin 1024 → Bool)
    (d : Usize) (rows : List Usize) : List word :=
  rows.filterMap (fun r => if (!flag active r) && (r != d) then some (lookup table r) else none)

theorem row_source (s q : word) (a : Bool) (r d : Usize) :
    prover_commit_reference.balance_m31_step (wrap s) (wrap q) a r d=
      (if (!a) && (r != d) then ok (wrap (add s q)) else ok (wrap s)) := by
  cases a <;> by_cases h : r=d <;>
    simp [prover_commit_reference.balance_m31_step,h,PV_L2C_ReferenceArithmetic.m31_add]
#print axioms row_source

theorem read_step (table : Fin 1024 → word) (active : Fin 1024 → Bool)
    (d r : Usize) (hr : r.val<1024) (s : word) :
    m31ReadStep (alloc.vec.Vec.deref (PV_L2C_VecRead.vector PV_L2C_VecRead.bound1024
      (fun i => wrap (table i)))) d (PV_L2C_VecRead.active active) r (wrap s)=
      (if (!flag active r) && (r != d) then ok (wrap (add s (lookup table r))) else ok (wrap s)) := by
  unfold m31ReadStep
  rw [PV_L2C_VecRead.read _ _ _ hr]
  simp only [bind_tc_ok]
  have hr' : r.val<(1024#usize).val := by scalar_tac
  rw [PV_L2C_VecRead.read_active (n:=1024#usize) active r hr']
  change prover_commit_reference.balance_m31_step (wrap s)
    (wrap (table ⟨r.val,hr⟩)) (active ⟨r.val,hr⟩) r d=_
  simp only [flag,lookup,dif_pos hr]
  exact row_wrap s (table ⟨r.val,hr⟩) (active ⟨r.val,hr⟩) r d
#print axioms read_step

theorem fold_source (table : Fin 1024 → word) (active : Fin 1024 → Bool)
    (d : Usize) (rows : List Usize) (hb : ∀ r∈rows,r.val<1024) (s : word) :
    foldSteps (m31ReadStep (alloc.vec.Vec.deref
      (PV_L2C_VecRead.vector PV_L2C_VecRead.bound1024 (fun i => wrap (table i))))
      d (PV_L2C_VecRead.active active)) rows (wrap s)=
        ok (wrap (PV_L2C_NativeFold.fold (selected table active d rows) s)) := by
  induction rows generalizing s with
  | nil => rfl
  | cons r rows ih =>
    have hr := hb r (by simp)
    have ht : ∀ x∈rows,x.val<1024 := fun x hx => hb x (by simp [hx])
    simp only [foldSteps,read_step table active d r hr,selected,List.filterMap_cons]
    split <;> simp only [bind_tc_ok,Option.toList_some,Option.toList_none,List.cons_append,
      List.nil_append,PV_L2C_NativeFold.fold] <;> exact ih ht _
#print axioms fold_source


open PV_L2C_VecRead PV_L2C_OwnedBalance

def output (table : Fin 1024 → word) (active : Fin 1024 → Bool) (d : Usize) : Fin 1024 → word :=
  fun i => if i.val=d.val then sub 0 (PV_L2C_NativeFold.fold (selected table active d rows) 0) else table i

theorem complete_result (table : Fin 1024 → word) (active : Fin 1024 → Bool)
    (d : Usize) (hd : d.val<1024) (ha : active ⟨d.val,hd⟩=false) :
    prover_commit_reference.balance_m31_owned
      (vector bound1024 (fun i => wrap (table i))) d (PV_L2C_VecRead.active active)=
      ok (.Ok (),vector bound1024 (fun i => wrap (output table active d i))) := by
  have hlen : alloc.vec.Vec.len (vector bound1024 (fun i => wrap (table i)))=1024#usize :=
    PV_L2C_VecShape.length bound1024 (fun i => wrap (table i))
  rw [m31_owned_fold,hlen]
  simp only [bne_self_eq_false,Bool.false_eq_true,if_false]
  rw [PV_L2C_VecShape.active_read active d hd]
  simp only [ha,bind_tc_ok,Bool.false_eq_true,if_false]
  have hz : aspis_core.field.M31.ZERO=wrap (0 : word) := rfl
  rw [hz,fold_source table active d (rowSequence 1024 0#usize) rows_bounded 0]
  simp only [bind_tc_ok,PV_L2C_ReferenceSub.m31_sub]
  rw [PV_L2C_VecBack.index_mut bound1024 _ d hd]
  simp only [bind_tc_ok]
  change ok ((core.result.Result.Ok () : core.result.Result Unit state_only_hiding.StateOnlyMaskBuildError),
    PV_L2C_VecBack.back (vector bound1024 (fun i => wrap (table i))) d
      (wrap (sub 0 (PV_L2C_NativeFold.fold (selected table active d rows) 0))))=_
  rw [PV_L2C_VecBack.write bound1024 _ d hd]
  have he : (fun i : Fin 1024 => if i.val=d.val then
      wrap (sub 0 (PV_L2C_NativeFold.fold (selected table active d rows) 0)) else wrap (table i))=
      (fun i => wrap (output table active d i)) := by
    funext i
    unfold output
    split <;> rfl
  rw [he]
#print axioms complete_result
end PV_L2C_ScalarBalance
