import R1Z.PrivacyR1AcctBasis
/-! Source-image obstruction to the literal "every model statement" target.
R0P.Public K uses wide-field cells and an unbounded Nat; the shipped public
record uses M31 cells and a u64 pair index. No byte error value is introduced.
These facts do not rule out an admitted/source-representable domain bridge. -/
set_option autoImplicit false
noncomputable section
namespace R1Z.ProverCommitPublicImage33
open R1Z.PrivacyR1AcctBasis

/-- Being typed in the wide field does not imply being an M31 source word. -/
theorem i_not_source_word :
    ¬ ∃ a : ZMod AspisCircleGroupOrder.P,
      algebraMap (ZMod AspisCircleGroupOrder.P) K a = i := by
  rintro ⟨a,h⟩
  have component := congrArg (fun z : K => z.re.re.im) h
  rw [base_coordinates] at component
  change (0 : ZMod AspisCircleGroupOrder.P) = 1 at component
  exact zero_ne_one component

/-- Every source-preserving asset image fails on a valid model record whose
assetId is i. This is independent of any chosen serialization or randomness. -/
theorem no_total_asset_image (initial : R0P.Public K)
    (image : R0P.Public K → ZMod AspisCircleGroupOrder.P) :
    ¬ ∀ p, algebraMap (ZMod AspisCircleGroupOrder.P) K (image p) = p.assetId := by
  intro preserve
  exact i_not_source_word ⟨image {initial with assetId := i},
    preserve {initial with assetId := i}⟩

/-- Canonical field values alone also do not bound the independent Nat index.
A source u64 is modeled here by its exact finite natural-value carrier. -/
theorem no_total_index_image {Field : Type} (initial : R0P.Public Field)
    (image : R0P.Public Field → Fin (2^64)) :
    ¬ ∀ p, (image p).val = p.nextPairIndex := by
  intro preserve
  let p := {initial with nextPairIndex := 2^64}
  have equal := preserve p
  have bound := (image p).isLt
  change (image p).val = 2^64 at equal
  omega

#print axioms i_not_source_word
#print axioms no_total_asset_image
#print axioms no_total_index_image
end R1Z.ProverCommitPublicImage33
