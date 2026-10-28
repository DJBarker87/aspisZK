import R1Z.PV_RunJoin_CompilerDictionary16
import R1Z.PV_RunJoin_ReferenceFixtureResults
import R1Z.PV_Src_Forest_TreeArguments
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_ChunkLift16
open Aeneas Aeneas.Std Result R0Z.WriterRefine R0Z.BuilderModel
variable {K : Type} [Field K] [CharP K 0x7fffffff]
-- The source chunk proof uses only the asset field of PubCorr.
theorem chunks (W : RustWitness) (P : RustPublic) (pub : R0P.Public K) (asset : liftU (K := K) P.asset = pub.assetId)
    (hW : WitnessOk W) : SabsOk pub (toModel W) (chunksOf W P) := by
  intro h hn hz
  obtain ⟨hv, hh⟩ := h
  dsimp only at hn hz ⊢
  have cases : hv = 0 ∨ hv = 1 ∨ hv = 2 ∨ hv = 3 ∨ hv = 25 ∨ hv = 26 ∨ hv = 27 ∨ hv = 28 ∨ hv = 29 ∨
      hv = 30 ∨ hv = 31 ∨ hv = 32 := by
    unfold NodeKind at hn; omega
  have v0 : liftU (K := K) W.inputValue = ((toModel (K := K) W).inputValue.val : K) := by
    show _ = ((W.inputValue.val % 2 ^ 30 : Nat) : K); rw [Nat.mod_eq_of_lt hW.values.1]; rfl
  have v1 : liftU (K := K) W.outputValue = ((toModel (K := K) W).outputValue.val : K) := by
    show _ = ((W.outputValue.val % 2 ^ 30 : Nat) : K); rw [Nat.mod_eq_of_lt hW.values.2.1]; rfl
  have v2 : liftU (K := K) W.changeValue = ((toModel (K := K) W).changeValue.val : K) := by
    show _ = ((W.changeValue.val % 2 ^ 30 : Nat) : K); rw [Nat.mod_eq_of_lt hW.values.2.2]; rfl
  rcases cases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact sabs_lo8 W.sk 8#usize n8 _ (fun i => rfl)
  · obtain ⟨d, hd, hdl, -⟩ := owner_lift (K := K) W
    have e : (chunksOf W P).schunk 1 = d := by show okOr (ownerD W) zero8 = d; rw [hd]; rfl
    rw [e]
    exact sabs_lo8 d 8#usize n8 _ hdl
  · exact sabs_c2 _ _ _ _ _ _ v0 asset (fun i => rfl) 8#usize n8
  · exact sabs_c3 _ _ (fun i => rfl) 2#usize n2
  · exact sabs_lo8 W.sk 8#usize n8 _ (fun i => rfl)
  · exact sabs_lo8 W.salt 8#usize n8 _ (fun i => rfl)
  · have htr := trv pub.variant 27 (by omega) (by omega) hz
    intro i
    show (recipB pub (toModel W) 0).absorb i = _
    unfold recipB; rw [htr]
    exact sabs_lo8 W.recipientOwner 8#usize n8 _ (fun i => rfl) i
  · have htr := trv pub.variant 28 (by omega) (by omega) hz
    intro i
    show (recipB pub (toModel W) 1).absorb i = _
    unfold recipB; rw [htr]
    exact sabs_c2 _ _ _ _ _ _ v1 asset (fun i => rfl) 8#usize n8 i
  · have htr := trv pub.variant 29 (by omega) (by omega) hz
    intro i
    show (recipB pub (toModel W) 2).absorb i = _
    unfold recipB; rw [htr]
    exact sabs_c3 _ _ (fun i => rfl) 2#usize n2 i
  · exact sabs_lo8 W.changeOwner 8#usize n8 _ (fun i => rfl)
  · exact sabs_c2 _ _ _ _ _ _ v2 asset (fun i => rfl) 8#usize n8
  · exact sabs_c3 _ _ (fun i => rfl) 2#usize n2

#print axioms chunks
end R1Z.PV_RunJoin_ChunkLift16
