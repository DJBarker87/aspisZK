import R1Z.PDict_Static222_PublicationFrame
set_option autoImplicit false
noncomputable section
namespace R1Z.PDict_Static222
open Aeneas Aeneas.Std ProverRwFull PDict_FormatterTypeMaps PDict_FormatterDictionaryMap


/-- Public carrier transport for the complete semantic proof consumer. -/
theorem erase_421 (base : ExternalTypes) (F : Type) (ops : @ExternalFuns base) :
    letI : ExternalTypes := base
    ∀ (public1 : Public) (variant : transport.Variant)
    (hash : Slice (Slice U8) → Result (Array U8 32#usize)) (backend : prover.Backend)
    (sem : host_semantic.BuiltSemantics aspis_core.digest.LegacyHashFn)
    (salts : aspis_prover.state_only_entropy.ReservedStateOnlyAttemptSecrets ×
      aspis_core.state_only_hiding.StateOnlyHidingContext),
    @prover.prove_from_semantics (types base F) (selected base F ops)
      (pub base F public1) variant hash backend sem salts =
    @prover.prove_from_semantics base ops public1 variant hash backend sem salts := by
  intro public1 variant hash backend sem salts
  delta prover.prove_from_semantics
  simp only [erase_341 base F ops, erase_372 base F ops, erase_392 base F ops, erase_420 base F ops,
    PDict_PublicLeaves222.bytes]
  all_goals rfl
#print axioms erase_421

/-- Full symbolic source-function equality for `prover.semantic_error`. -/
theorem erase_422 (base : ExternalTypes) (F : Type) (ops : @ExternalFuns base) :
    @prover.semantic_error (types base F) (selected base F ops) = @prover.semantic_error base ops := by
  delta prover.semantic_error
  all_goals rfl
#print axioms erase_422

end R1Z.PDict_Static222
