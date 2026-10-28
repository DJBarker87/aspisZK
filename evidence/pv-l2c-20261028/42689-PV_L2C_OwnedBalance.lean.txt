import PV_L2C_ExtractedRows
import PV_L2C_VecWrite
set_option autoImplicit false
namespace PV_L2C_OwnedBalance
open Aeneas Aeneas.Std Result AspisR1ProverBalance9
open PV_L2C_NativeQ PV_L2C_QBalance PV_L2C_ReferenceQ PV_L2C_ExtractedRows PV_L2C_VecRead
open R1Z.ProverCommitBalanceRecursion

def rows : List Usize := rowSequence 1024 0#usize

theorem rows_bounded : ∀ r∈rows,r.val<1024 := by
  intro r hr
  have hm : r.val∈rows.map (fun r => r.val) := List.mem_map.mpr ⟨r,hr,rfl⟩
  rw [rows,sequence_ascending 1024 0#usize (by decide)] at hm
  have hb := List.mem_range'.mp hm
  have hz : (0#usize).val=0 := by scalar_tac
  rw [hz] at hb
  omega
#print axioms rows_bounded

def output (table : Fin 1024 → Q) (active : Fin 1024 → Bool) (d : Usize) : Fin 1024 → Q :=
  fun i => if i.val=d.val then subQ zero (foldQ (selected table active d rows) zero) else table i

theorem complete_result (table : Fin 1024 → Q) (active : Fin 1024 → Bool)
    (d : Usize) (hd : d.val<1024) (ha : active ⟨d.val,hd⟩=false) :
    prover_commit_reference.balance_qm31_owned
      (vector bound1024 (fun i => source (table i))) d (PV_L2C_VecRead.active active)=
      ok (.Ok (),vector bound1024 (fun i => source (output table active d i))) := by
  have hlen : alloc.vec.Vec.len (vector bound1024 (fun i => source (table i)))=1024#usize := by
    apply UScalar.eq_of_val_eq
    change (List.ofFn (fun i => source (table i))).length=1024
    exact List.length_ofFn
  have hd' : d.val<(1024#usize).val := by scalar_tac
  rw [qm31_owned_fold,hlen]
  simp only [bne_self_eq_false,Bool.false_eq_true,if_false]
  rw [read_active (n:=1024#usize) active d hd']
  simp only [ha,bind_tc_ok,Bool.false_eq_true,if_false]
  rw [← source_zero,fold_source table active d rows rows_bounded zero]
  simp only [bind_tc_ok,sub_source]
  rw [PV_L2C_VecWrite.index_mut bound1024 _ d hd]
  simp only [bind_tc_ok]
  rw [PV_L2C_VecWrite.write bound1024 _ d hd]
  have he : (fun i : Fin 1024 => if i.val=d.val then
      source (subQ zero (foldQ (selected table active d rows) zero)) else source (table i))=
      (fun i => source (output table active d i)) := by
    funext i
    unfold output
    split <;> rfl
  rw [he]
#print axioms complete_result
end PV_L2C_OwnedBalance
