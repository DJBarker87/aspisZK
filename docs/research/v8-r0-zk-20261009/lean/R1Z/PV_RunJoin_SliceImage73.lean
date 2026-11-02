import R1Z.PV_RunJoin_MergeArray35
set_option autoImplicit false
namespace R1Z.PV_RunJoin_SliceImage73
open Aeneas Aeneas.Std Result

theorem complete {T : Type} (s : Slice T) (count : Usize) (f : Nat → T)
    (size : s.length=count.val)
    (agrees : ∀ i : Usize,i.val<count.val → Slice.index_usize s i=ok (f i.val)) :
    s=Array.to_slice (ProverCommitArray49.array count f) := by
  apply Subtype.ext
  apply List.ext_getElem
  · simpa only [ProverCommitArray49.array,Array.to_slice,List.length_ofFn] using size
  · intro k hk hk'
    have bound : k<count.val := by rw [←size];exact hk
    have max : count.val ≤ Usize.max := by scalar_tac
    let i := Usize.ofNatCore k (by omega)
    have iv : i.val=k := by simp only [i,UScalar.ofNatCore_val_eq]
    have hi : i.val<s.length := by rw [iv,size];exact bound
    obtain ⟨v,read,hv⟩ := WP.spec_imp_exists (Slice.index_usize_spec s i hi)
    have eq := Result.ok.inj (read.symm.trans (agrees i (by rw [iv];exact bound)))
    rw [hv] at eq
    simpa only [ProverCommitArray49.array,Array.to_slice,List.getElem_ofFn,iv] using eq

#print axioms complete
end R1Z.PV_RunJoin_SliceImage73
