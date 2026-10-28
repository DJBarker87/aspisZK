import R1Z.PV_RunJoin_NativePublicInverse32
import R1Z.PV_RunJoin_NativeSelectedInputs
import R1Z.PV_RunJoin_HonestIdentification26
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_SelectedCoordinates32
open Aeneas Aeneas.Std Result R0Z.WriterRefine R1J.SpendWitnessMap
open PV_RunJoin_NativePublicInverse32 PV_RunJoin_HonestIdentification26
variable {K : Type} [Field K] [Fintype K] [DecidableEq K]
  [Algebra (ZMod AspisCircleGroupOrder.P) K] [CharP K 2147483647]

def semantic (base : ProverRwFull.ExternalTypes)
    (pub : PV_RunJoin_NominalPublicData.TargetPublic base) : R0P.Public K :=
  mapPub (PV_Src_Public.canonicalPublic (unPublic base pub))

/-- The complete nominal public argument projects to the canonical source
statement for the same honest input, without an identification premise. -/
theorem public_coordinate (base : ProverRwFull.ExternalTypes) (i : Honest (K := K)) :
    semantic base (PV_RunJoin_NominalPublicData.fromInput base i.val) =
      BuilderSource.prover.public (target i) := by
  rw [semantic,from_input_roundtrip]
  exact (PV_RunJoin_UniversalPublic22.projection (inputs (K := K))
    PV_Src_Transport.transport i).symm.trans (public_eq i)
#print axioms public_coordinate

local instance : ProverRwRngCaller.NativeTypes := PV_RunJoin_CallerWorld.nativeTypes
local instance : ProverRwRngCaller.ErasureFns := ⟨fun _ value => .ok value,fun _ value => .ok value⟩

/-- This is the public coordinate of the actual full emitted-body input
record, universally over source states and the retained primitive dictionary. -/
theorem caller_public {N C : Type} (base : ProverRwFull.ExternalTypes)
    (ops : PV_RunJoin_NativeSelectedInputs.SourceState base N C →
      @ProverRwFull.ExternalFuns (PDict_CodecDictionary.native base))
    (hash : Slice (Slice U8) → Result (Array U8 32#usize))
    (i : Honest (K := K)) (s : PV_RunJoin_NativeSelectedInputs.SourceState base N C) :
    letI : ProverRwFull.ExternalTypes := PDict_CodecDictionary.native base
    semantic base ((PV_RunJoin_NativeSelectedInputs.inputs base ops hash i.val).pub s) =
      BuilderSource.prover.public (target i) := by
  letI : ProverRwFull.ExternalTypes := PDict_CodecDictionary.native base
  exact public_coordinate base i
#print axioms caller_public

/-- All translated merged C1 columns equal the unchanged canonical builder
trace for the SAME input. This is not equality between different witnesses. -/
theorem caller_columns {N C : Type} (base : ProverRwFull.ExternalTypes)
    (ops : PV_RunJoin_NativeSelectedInputs.SourceState base N C →
      @ProverRwFull.ExternalFuns (PDict_CodecDictionary.native base))
    (hash : Slice (Slice U8) → Result (Array U8 32#usize))
    (i : Honest (K := K)) (s : PV_RunJoin_NativeSelectedInputs.SourceState base N C) :
    letI : ProverRwFull.ExternalTypes := PDict_CodecDictionary.native base
    PV_Src_NativeInput.columns PV_Src_Forest_Columns.read
      ((PV_RunJoin_NativeSelectedInputs.inputs base ops hash i.val).compiled s).semantic_c1.c1 =
      BuilderSource.prover.build (target i) := by
  letI : ProverRwFull.ExternalTypes := PDict_CodecDictionary.native base
  exact build_eq i
#print axioms caller_columns
end R1Z.PV_RunJoin_SelectedCoordinates32
