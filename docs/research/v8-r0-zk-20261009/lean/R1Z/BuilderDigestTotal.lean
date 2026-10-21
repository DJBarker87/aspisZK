import R1Z.BuilderDigestArguments

/-! Totality of canonical digest primitives for arbitrary raw words. This
uses symbolic finite-field refinement, not evaluation of a permutation. -/
set_option autoImplicit false
noncomputable section
namespace R1Z.BuilderDigestTotal
open Aeneas Aeneas.Std Result R0Z.WriterRefine

theorem bind_total {A B : Type} (x : Result A) (f : A → Result B)
    (hx : ∃ a, x = ok a) (hf : ∀ a, ∃ b, f a = ok b) :
    ∃ b, (do let a ← x; f a) = ok b := by
  obtain ⟨a,ha⟩ := hx
  obtain ⟨b,hb⟩ := hf a
  exact ⟨b,by rw [ha];simpa only [bind_tc_ok] using hb⟩

theorem perm_total (pre ab : Array U32 16#usize) :
    ∃ rounds, R0PoseidonCopy.perm_rounds pre ab = ok rounds := by
  let B : R0Z.BuilderModel.BlockIn (ZMod AspisCircleGroupOrder.P) :=
    ⟨fun i => liftU pre.val[i.val]!,fun i => liftU ab.val[i.val]!⟩
  obtain ⟨rounds,hr,_⟩ := R0Z.PoseidonRefine.perm_rounds_lift pre ab B
    (by constructor <;> intro i <;> rfl)
  exact ⟨rounds,hr⟩

theorem block_total (pre ab : Array U32 16#usize) : ∃ d, blockDigestR pre ab = ok d := by
  obtain ⟨rounds,hr⟩ := perm_total pre ab
  exact ⟨_,by rw [blockDigestR,hr];rfl⟩

theorem sponge_total (pre : Array U32 16#usize) (chunk : Array U32 8#usize) (len : Usize) :
    ∃ d, spongeDigestR pre chunk len = ok d := by
  unfold spongeDigestR
  apply bind_total
  · obtain ⟨ab,ha,_⟩ := sponge_absorb_spec chunk len;exact ⟨ab,ha⟩
  · intro ab;exact block_total pre ab

theorem step_total (pre : Array U32 16#usize) (chunk : Array U32 8#usize) (len : Usize) :
    ∃ s, spongeStep pre chunk len = ok s := by
  obtain ⟨ab,ha,_⟩ := sponge_absorb_spec chunk len
  obtain ⟨rounds,hr⟩ := perm_total pre ab
  exact ⟨_,by rw [spongeStep,ha];simp only [bind_tc_ok];rw [hr];rfl⟩

theorem init_total (tag len : U32) : ∃ s, R0BlockCopies.sponge_init tag len = ok s := by
  obtain ⟨s,hs,_⟩ := sponge_init_spec tag len
  exact ⟨s,hs⟩

theorem pre_total (R : RustChunks) (h : Nat) : ∃ s, spongePre R h = ok s := by
  unfold spongePre
  split <;>
    repeat first
      | exact init_total _ _
      | exact step_total _ _ _
      | apply bind_total
      | intro s
      | exact ⟨_,rfl⟩

theorem note_total (R : RustChunks) (h : Nat) : ∃ d, noteDigestR R h = ok d := by
  unfold noteDigestR
  apply bind_total _ _ (pre_total R h)
  intro s;exact sponge_total s _ _

#print axioms bind_total
#print axioms perm_total
#print axioms block_total
#print axioms sponge_total
#print axioms step_total
#print axioms init_total
#print axioms pre_total
#print axioms note_total
end R1Z.BuilderDigestTotal
