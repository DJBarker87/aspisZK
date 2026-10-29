import R1Z.PV_RunJoin_PrepareTailAssociation48
import R1Z.PV_RunJoin_ScalarSource49
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_TailScalar49
open Aeneas Aeneas.Std Result ProverRwFull
open PV_RunJoin_WeightInstalled46
open PV_RunJoin_PreparedDomain48 (W)
variable [ExternalTypes] [ExternalFuns]
def after (backend : prover.Backend) (sem : host_semantic.BuiltSemantics aspis_core.digest.LegacyHashFn)
    (y1 : alloc.vec.Vec U8) (gamma inactive kappa : W) (bytes : alloc.vec.Vec U8)
    (q w : Slice W) (fold : Slice W → W → Bool → Result (alloc.vec.Vec W))
    (scalar : Result (W × host_transcript.Transcript aspis_core.digest.LegacyHashFn)) := do
  let (a,next) ← scalar
  let q1 ← fold q a false
  let w1 ← fold w a true
  PV_RunJoin_PreparedDomain48.run backend sem next y1 gamma inactive kappa a bytes q1 w1
    (host_commitment.EncodingDomain.evaluate aspis_core.field.wide_exact.WideExact.Insts.Aspis_coreR0ScalarCodeField
      backend.domain (alloc.vec.Vec.deref q1) 0#usize)

theorem source (variant : transport.Variant) (hash : Slice (Slice U8) → Result (Array U8 32#usize))
    (backend : prover.Backend) (sem : host_semantic.BuiltSemantics aspis_core.digest.LegacyHashFn)
    (tr : host_transcript.Transcript aspis_core.digest.LegacyHashFn)
    (y1 : alloc.vec.Vec U8) (gamma inactive kappa : W) (bytes : alloc.vec.Vec U8)
    (q w : Slice W) (fold : Slice W → W → Bool → Result (alloc.vec.Vec W)) :
    PV_RunJoin_PrepareTailAssociation48.retained variant hash backend sem tr y1 gamma inactive kappa bytes q w fold=
      after backend sem y1 gamma inactive kappa bytes q w fold
        (host_transcript.Transcript.scalar aspis_core.digest.LegacyHashFn.Insts.Aspis_coreDigestDigest32
          tr 29#u8 (alloc.vec.Vec.deref bytes) false) := rfl

end R1Z.PV_RunJoin_TailScalar49
namespace R1Z.PV_RunJoin_TailScalar49
open Aeneas Aeneas.Std Result ProverRwFull
open PV_RunJoin_WeightInstalled46
open PV_RunJoin_PreparedDomain48 (W)
set_option allowUnsafeReducibility true in
attribute [local irreducible] ProverRwP6BoundaryInstall.selected
attribute [local irreducible] selected PV_B2_F_RawNative.selected PV_B2_F_ResourceFamilies.selected

theorem complete (base : ExternalTypes) (heap : Heap) (box : Box) (ops : @ExternalFuns (types base))
    (variant : transport.Variant) (hash : Slice (Slice U8) → Result (Array U8 32#usize))
    (backend : prover.Backend) (sem : host_semantic.BuiltSemantics aspis_core.digest.LegacyHashFn)
    (tr : host_transcript.Transcript aspis_core.digest.LegacyHashFn)
    (y1 : alloc.vec.Vec U8) (gamma inactive kappa : W) (bytes : alloc.vec.Vec U8)
    (q w : Slice W) (fold : Slice W → W → Bool → Result (alloc.vec.Vec W)) :
    @PV_RunJoin_PrepareTailAssociation48.retained (types base) (selected base heap box ops)
      variant hash backend sem tr y1 gamma inactive kappa bytes q w fold=
      @after (types base) (selected base heap box ops) backend sem y1 gamma inactive kappa bytes q w fold
        (PV_RunJoin_ScalarSource49.retained base heap box ops
          (@aspis_core.digest.LegacyHashFn.Insts.Aspis_coreDigestDigest32 (types base) (selected base heap box ops))
          tr 29#u8 (alloc.vec.Vec.deref bytes) false) := by
  letI : ExternalTypes := types base
  letI : ExternalFuns := selected base heap box ops
  rw [source,PV_RunJoin_ScalarSource49.complete]
#print axioms after
#print axioms source
#print axioms complete
end R1Z.PV_RunJoin_TailScalar49
