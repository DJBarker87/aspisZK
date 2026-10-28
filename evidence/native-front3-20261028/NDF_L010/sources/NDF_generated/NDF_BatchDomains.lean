import NDF_LeafBridge
import NDF_OpeningBridge
import Port4B_Opening
set_option autoImplicit false
namespace NDF_BatchDomains
open Aeneas Aeneas.Std Result

theorem position (batch pos : Nat) (active : pos < (if batch=0 then 10 else 12)) :
    pos < 16 ∧ (if batch=0 then 0 else 10)+pos < 22 := by
  split_ifs at * <;> omega

theorem duplicate (batch pos d : Nat)
    (active : pos < (if batch=0 then 10 else 12)) (count : d ≤ pos) (positive : 0<d) :
    d-1 < 16 := by
  have := position batch pos active
  omega

theorem key_read (keys : Array U64 16#usize) (i : Usize) (bound : i.val < 16) :
    ∃ value, NDF_Reference.batch_key_at_ref keys i=ok value ∧ value=keys.val[i.val]'(by simpa [keys.property] using bound) := by
  exact WP.spec_imp_exists (Array.index_usize_spec keys i bound)

theorem index_read (values : Array U32 16#usize) (i : Usize) (expected : U32) (bound : i.val<16) :
    NDF_Reference.same_batch_index_ref values i expected =
      ok (decide (values.val[i.val]'(by simpa [values.property] using bound)=expected)) := by
  obtain ⟨value,read,same⟩ := WP.spec_imp_exists (Array.index_usize_spec values i bound)
  rw [NDF_ScalarBridge.same_index]
  exact (AspisR1.Port3_BatchStd.same_index_read values i expected value read).trans (by rw [same])

theorem opening_exact (proof : Slice U8) (len : proof.val.length=57607)
    (i : Usize) (bound : i.val<22) :
    ∃ view, NDF_Reference.opening_ref proof i=ok view ∧ view.val.length=832 ∧
      AspisV8R19.DuplexFrames.bytesOf view.val=OraclePortCompactDraft.slice
        (AspisV8R19.DuplexFrames.bytesOf proof.val) (10055+i.val*832) 832 := by
  rw [NDF_OpeningBridge.reference proof i bound]
  exact AspisR1.Port4B_Opening.opening_exact proof len i bound

#print axioms position
#print axioms duplicate
#print axioms key_read
#print axioms index_read
#print axioms opening_exact
end NDF_BatchDomains
