import CuSavingsS2SourceArrays
import CuSavingsS2SourceSearch
set_option autoImplicit false
namespace AspisR1.CuSavingsS2SourceCatalog
open Aeneas Aeneas.Std Result AspisR1S2Groups
open CuSavingsS2SourceArrays CuSavingsS2SourceTables

theorem search_from_catalog (pos : Nat) (hp : pos<64) (masks : Masks) (groups target : Usize)
    (mask : U16) (hc : Catalog pos masks groups)
    (ht : target.val=CuSavingsS2Tables.groupValue ⟨pos,hp⟩) (hlt : target.val<12)
    (hm : mask.val=CuSavingsS2Tables.masks.getD target.val 0) :
    old.grouped_inactive_pair_loop0_loop1 masks groups mask 0#usize = .ok target := by
  have step := catalog_step ⟨pos,hp⟩
  dsimp only at step
  have hcount := hc.1
  apply CuSavingsS2SourceSearch.source_find target.val masks groups target 0#usize mask
    (by scalar_tac) (by omega) (by omega) (by scalar_tac)
  · intro i hi
    have hi64 : i.val<masks.val.length := by scalar_tac
    refine ⟨lookup masks 0#u16 i.val,read masks 0#u16 i hi64,?_⟩
    intro he
    have hv:=congrArg UScalar.val he
    rw [hc.2 i.val (by omega),hm] at hv
    exact mask_distinct ⟨i.val,by omega⟩ ⟨target.val,hlt⟩
      (by intro he;have hval:=congrArg Fin.val he;omega) hv
  · intro hi
    have hr := read masks 0#u16 target (by scalar_tac)
    have he : lookup masks 0#u16 target.val=mask := UScalar.eq_of_val_eq
      ((hc.2 target.val hi).trans hm.symm)
    simpa only [he] using hr

def extend (masks : Masks) (groups group : Usize) (mask : U16) : Result (Masks × Usize) := do
  if group=groups then
    let masks1 ← Array.update masks group mask
    let groups1 ← groups+1#usize
    .ok (masks1,groups1)
  else .ok (masks,groups)

theorem extend_success (pos : Nat) (hp : pos<64) (masks : Masks) (groups group : Usize)
    (mask : U16) (hc : Catalog pos masks groups)
    (hg : group.val=CuSavingsS2Tables.groupValue ⟨pos,hp⟩) (hlt : group.val<12)
    (hm : mask.val=CuSavingsS2Tables.masks.getD group.val 0) :
    ∃ masks1 groups1, extend masks groups group mask = .ok (masks1,groups1) ∧
      Catalog (pos+1) masks1 groups1 := by
  have step := catalog_step ⟨pos,hp⟩
  dsimp only at step
  have hcount := hc.1
  by_cases he : group=groups
  · have heval := congrArg UScalar.val he
    have hseen : seen (pos+1)=groups.val+1 := by
      have hmatch : CuSavingsS2Tables.groupValue ⟨pos,hp⟩=seen pos := by omega
      simpa only [hmatch,↓reduceIte,←hcount] using step.2.2
    obtain ⟨groups1,hn,hnv⟩ := WP.spec_imp_exists (UScalar.add_spec (x:=groups) (y:=1#usize) (by scalar_tac))
    have hone : (1#usize).val=1 := by scalar_tac
    rw [hone] at hnv
    refine ⟨masks.set group mask,groups1,?_,?_,?_⟩
    · simp only [extend,if_pos he,update masks group mask (by scalar_tac),hn,bind_tc_ok]
    · rw [hnv,hseen]
    · intro i hi
      rw [lookup_set masks 0#u16 group (by scalar_tac)]
      by_cases hsame : i=group.val
      · simp only [hsame,↓reduceIte]
        exact hm
      · simp only [hsame,↓reduceIte]
        exact hc.2 i (by omega)
  · have hne : group.val ≠ groups.val := by intro h;exact he (UScalar.eq_of_val_eq h)
    have hseen : seen (pos+1)=seen pos := by
      have hmatch : CuSavingsS2Tables.groupValue ⟨pos,hp⟩ ≠ seen pos := by omega
      simpa only [hmatch,↓reduceIte] using step.2.2
    refine ⟨masks,groups,by simp only [extend,if_neg he],?_,hc.2⟩
    rw [hseen]
    exact hcount

#print axioms search_from_catalog
#print axioms extend_success
end AspisR1.CuSavingsS2SourceCatalog
