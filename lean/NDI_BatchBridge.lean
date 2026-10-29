import NDI_BatchRun
set_option autoImplicit false
noncomputable section
namespace NDI_BatchBridge
open Aeneas Aeneas.Std Result AspisR1

theorem reference (raw : Array U32 22#usize) (lo n tree : Usize) (batch : Nat)
    (lower : lo.val=(if batch=0 then 0 else 10))
    (count : n.val=(if batch=0 then 10 else 12))
    (canonical : ∀ k, k<22 → raw.val[k]!.val<262144) :
    NDI_BatchRef.batch_keys_ref raw lo n tree =
      ok (Port4B_KeyInstall.keyArray raw batch tree.val) := by
  let word := fun j => MultiproofConeSortOrder.packed (Port4B_KeyInstall.queries raw)
    batch tree.val ((if batch=0 then 0 else 10)+j)
  have size : n.val≤16 := by rw [count];split <;> omega
  have fit : lo.val+n.val≤22 := by rw [lower,count];split <;> omega
  have tag : (tree=2#usize) ↔ tree.val=2 := by
    constructor
    · intro h;subst tree;rfl
    · intro h;exact UScalar.eq_of_val_eq h
  have spec : ∀ k, k<n.val → (word k).val=
      256*(if tree=2#usize then raw.val[lo.val+k]!.val/4
        else raw.val[lo.val+k]!.val)+k := by
    intro k active
    have bound : (if batch=0 then 0 else 10)+k<22 := by omega
    have h := NBI_Keys.packed_word raw batch tree.val k (by omega) (canonical _ bound)
    simpa only [word,lower,tag] using h
  obtain ⟨out,call,cells⟩ := NDI_BatchRun.run raw lo n tree 0#usize
    (Array.repeat 16#usize 0#u64) word size fit (by simp) spec
  have equal : out=Port4B_KeyInstall.keyArray raw batch tree.val := by
    apply Subtype.ext
    apply List.ext_getElem
    · exact out.property.trans (Port4B_KeyInstall.keyArray raw batch tree.val).property.symm
    · intro k ha hb
      have kb : k<16 := by have length : out.val.length=16 := out.property;omega
      have h := cells k
      have init : (fun c : Nat => (Array.repeat 16#usize 0#u64).val[c]!) = (fun _ => 0#u64) := by
        funext c
        simp only [Array.repeat,List.getElem!_eq_getElem?_getD,List.getElem?_replicate]
        split <;> rfl
      rw [init] at h
      have old := NBI_Keys.key_array_values raw batch tree.val k kb
      change out.val[k]! =NBE_KeyLoop.fill word n.val 0 (fun _ => 0#u64) k at h
      rw [count] at h
      simpa only [word,
        List.getElem!_eq_getElem?_getD,List.getElem?_eq_getElem ha,
        List.getElem?_eq_getElem hb,Option.getD_some] using h.trans old
  simp only [NDI_BatchRef.batch_keys_ref,call, equal]

#print axioms reference
end NDI_BatchBridge
