import R1Z.PV_RunJoin_WeightInstalled46
import R1Z.PV_RunJoin_CallerSuccess43
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_SemanticFrame66
open Aeneas Aeneas.Std Result ProverRwFull PV_RunJoin_WeightInstalled46
abbrev Q := aspis_core.field.QM31

/-- The weight-only installations must not alter the semantic byte builder.
Both sides retain identical digest, helper and commitment dictionaries. -/
theorem helper (base : ExternalTypes) (heap : Heap) (box : Box)
    (ops : @ExternalFuns (types base)) {H T1 T2 : Type} (D : aspis_core.digest.Digest32 H)
    (worker : core.ops.function.FnOnce T1 (Q × Q) (core.result.Result (alloc.vec.Vec Q) r1_wire.Error))
    (commit : host_semantic.Commitments T2)
    (public1 : @aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public (types base))
    (columns : Array (alloc.vec.Vec aspis_core.field.M31) 26#usize)
    (d g padding : Array Q 1024#usize) (input : T1) (state : T2) (hash : H) (variant : transport.Variant) :
    @host_semantic.build_with_helper_mode (types base) (selected base heap box ops)
      H T1 T2 D worker commit public1 columns d g padding input state hash variant=
    @host_semantic.build_with_helper_mode (types base) (@ProverRwP6BodyCandidate.selected (types base) ops)
      H T1 T2 D worker commit public1 columns d g padding input state hash variant := by
  rfl

#print axioms helper
end R1Z.PV_RunJoin_SemanticFrame66
