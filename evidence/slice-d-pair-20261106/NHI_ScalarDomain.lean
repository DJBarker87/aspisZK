import NHI_ScalarStep
set_option autoImplicit false
namespace NHI_ScalarDomain
open Aeneas Aeneas.Std Result AspisR1 LPi_FieldValues

def pick {α : Type} {n : Usize} (a : Array α n) (i : Nat) (h : i<n.val) : α :=
 a.val[i]'(by rw [a.property];exact h)

theorem index {α : Type} {n : Usize} (a : Array α n) (i : Usize) (h : i.val<n.val) :
 Array.index_usize a i=ok (pick a i.val h) := by
 simp [Array.index_usize,pick,h]

theorem perm (s : Usize) (h : s.val<4) :
 ∃ i, Array.index_usize FIo_Native.weights.PERM s=ok i ∧ i.val<4 := by
 have cases : s=0#usize ∨ s=1#usize ∨ s=2#usize ∨ s=3#usize := by
  have : s.val=0 ∨ s.val=1 ∨ s.val=2 ∨ s.val=3 := by omega
  rcases this with h|h|h|h
  · exact Or.inl (UScalar.eq_of_val_eq h)
  · exact Or.inr (Or.inl (UScalar.eq_of_val_eq h))
  · exact Or.inr (Or.inr (Or.inl (UScalar.eq_of_val_eq h)))
  · exact Or.inr (Or.inr (Or.inr (UScalar.eq_of_val_eq h)))
 rcases cases with rfl|rfl|rfl|rfl
 · exact ⟨0#usize,by unfold FIo_Native.weights.PERM;rfl,by decide⟩
 · exact ⟨3#usize,by unfold FIo_Native.weights.PERM;rfl,by decide⟩
 · exact ⟨2#usize,by unfold FIo_Native.weights.PERM;rfl,by decide⟩
 · exact ⟨1#usize,by unfold FIo_Native.weights.PERM;rfl,by decide⟩

theorem canon_pick {α : Type} (P : α → Prop) {n : Usize} (a : Array α n)
 (all : ∀ x∈a.val,P x) (i : Nat) (h : i<n.val) : P (pick a i h) := by
 apply all
 exact List.mem_of_getElem? (show a.val[i]?=some (pick a i h) by
  simp [pick,show i<a.val.length by rw [a.property];exact h])

/-- Every scalar callee domain is derived from the SAME two input arrays. -/
theorem total (p : Array NE 4#usize) (f : Array NQ 4#usize)
 (hp : ∀ x∈p.val,canonE x) (hf : ∀ x∈f.val,canonQ x)
 (v : NE) (hv : canonE v) (s : Usize) (hs : s.val<4) :
 ∃ out,FIo_Native.weights.Weights.scalar_factor.closure.Insts.CoreOpsFunctionFnMutPairWideExactUsizeWideExact.call_mut
 (p,f) (v,s)=ok (out,(p,f)) ∧ canonE out := by
 obtain ⟨i,hi,ib⟩ := perm s hs
 obtain ⟨out,run,co⟩ := NHI_ScalarStep.observed p f v (pick p i.val ib) (pick f s.val hs) s i
  hi (index p i ib) (index f s hs) (canon_pick canonE p hp i.val ib)
  (canon_pick canonQ f hf s.val hs) hv
 exact ⟨out,(NHI_ScalarStep.emitted p f v s).symm.trans run,co⟩

#print axioms index
#print axioms perm
#print axioms canon_pick
#print axioms total
end NHI_ScalarDomain
