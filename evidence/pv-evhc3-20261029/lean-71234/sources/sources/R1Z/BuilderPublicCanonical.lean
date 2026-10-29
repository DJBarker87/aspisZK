import R1Z.BuilderRecordCanonical

/-! Public record reconstruction, including the exact frozen empty roots.
PubCorr is over M31 here, so its equality retains canonical-word identity.
The runtime still owes PubCorr for the computed pair_empty_roots result. -/
set_option autoImplicit false
noncomputable section
namespace R1Z.BuilderPublicCanonical
open Aeneas Aeneas.Std R0Z.WriterRefine R0Z.BuilderModel
open R1J.SpendWitnessMap R1Z.BuilderRecordCanonical

theorem frozen_word (l : Fin 20) (i : Fin 8) :
    w32 (emptyRootK (K := F) l i) = emptyWord l i := by
  apply UScalar.eq_of_val_eq
  rw [w32_val, emptyWord, UScalar.ofNatCore_val_eq]
  change ((R0P.emptyRootsNat l.castSucc i : Nat) : ZMod 2147483647).val = _
  rw [ZMod.val_natCast, Nat.mod_eq_of_lt (emptyRoot_lt _ _)]

/-- Reconstruct every public-record field. Empty roots are fixed by PubCorr,
not inferred from arbitrary-root record projection equivalence. -/
theorem public_roundtrip (p : RustPublic) (pub : R0P.Public F)
    (hp : PubCorr p pub) (ha : p.asset.val < 2147483647) :
    toRustPub pub = p := by
  unfold toRustPub
  congr 1
  · exact hp.variant.symm
  · rw [← hp.asset]
    exact word_roundtrip _ ha
  · exact hp.next.symm
  · apply array_ext
    intro l hl
    rw [arr20_get _ l (by simpa using hl)]
    apply array_ext
    intro i hi
    rw [d32, arr8_get _ i (by simpa using hi)]
    rw [← hp.frontier ⟨l, by simpa using hl⟩ ⟨i, by simpa using hi⟩]
    exact word_roundtrip _ (hp.frontierCanon ⟨l, by simpa using hl⟩ i (by simpa using hi))
  · apply array_ext
    intro l hl
    rw [arr20_get _ l (by simpa using hl)]
    apply array_ext
    intro i hi
    rw [arr8_get _ i (by simpa using hi), ← frozen_word]
    rw [← hp.empty ⟨l, by simpa using hl⟩ ⟨i, by simpa using hi⟩]
    exact word_roundtrip _ (hp.emptyCanon ⟨l, by simpa using hl⟩ i (by simpa using hi))

#print axioms frozen_word
#print axioms public_roundtrip
end R1Z.BuilderPublicCanonical
