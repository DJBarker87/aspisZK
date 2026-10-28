import PV_L2C_VecRead
import PV_L2C_ReferenceQ
import PV_L2C_QFold
set_option autoImplicit false
namespace PV_L2C_ExtractedRows
open Aeneas Aeneas.Std Result AspisR1ProverBalance9
open PV_L2C_NativeQ PV_L2C_ReferenceQ PV_L2C_QFold
open R1Z.ProverCommitFoldSteps R1Z.ProverCommitBalanceRecursion

def lookup (table : Fin 1024 → Q) (r : Usize) : Q :=
  if h : r.val<1024 then table ⟨r.val,h⟩ else zero

def flag (active : Fin 1024 → Bool) (r : Usize) : Bool :=
  if h : r.val<1024 then active ⟨r.val,h⟩ else true

def selected (table : Fin 1024 → Q) (active : Fin 1024 → Bool)
    (d : Usize) (rows : List Usize) : List Q :=
  rows.filterMap (fun r => if !flag active r && r!=d then some (lookup table r) else none)

theorem read_step (table : Fin 1024 → Q) (active : Fin 1024 → Bool)
    (d r : Usize) (hr : r.val<1024) (s : Q) :
    qm31ReadStep (alloc.vec.Vec.deref (PV_L2C_VecRead.vector PV_L2C_VecRead.bound1024
      (fun i => source (table i)))) d (PV_L2C_VecRead.active active) r (source s)=
      (if !flag active r && r!=d then ok (source (addQ s (lookup table r))) else ok (source s)) := by
  unfold qm31ReadStep
  rw [PV_L2C_VecRead.read _ _ _ hr]
  simp only [bind_tc_ok]
  rw [PV_L2C_VecRead.read_active _ _ hr]
  simp only [bind_tc_ok, qm31_row, flag,lookup,dif_pos hr]
  split <;> simp only [add_source]
#print axioms read_step

theorem fold_source (table : Fin 1024 → Q) (active : Fin 1024 → Bool)
    (d : Usize) (rows : List Usize) (hb : ∀ r∈rows,r.val<1024) (s : Q) :
    foldSteps (qm31ReadStep (alloc.vec.Vec.deref
      (PV_L2C_VecRead.vector PV_L2C_VecRead.bound1024 (fun i => source (table i))))
      d (PV_L2C_VecRead.active active)) rows (source s)=
        ok (source (foldQ (selected table active d rows) s)) := by
  induction rows generalizing s with
  | nil => rfl
  | cons r rows ih =>
    have hr := hb r (by simp)
    have ht : ∀ x∈rows,x.val<1024 := fun x hx => hb x (by simp [hx])
    simp only [foldSteps,read_step table active d r hr,selected,List.filterMap_cons]
    split <;> simp only [bind_tc_ok,Option.toList_some,Option.toList_none,List.cons_append,
      List.nil_append,foldQ] <;> exact ih ht _
#print axioms fold_source

#print core.slice.index.Usize.index_mut
#print alloc.vec.Vec.index_mut
end PV_L2C_ExtractedRows
