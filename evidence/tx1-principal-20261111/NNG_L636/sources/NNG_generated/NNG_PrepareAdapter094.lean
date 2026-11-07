import NNG_Context094
import NNG_Producer087
set_option autoImplicit false
noncomputable section
namespace AspisR1.NNG_PrepareAdapter094
open Aeneas Aeneas.Std Result NMT_tx1
open NNG_Carriers094
open NMT_Transport (arr)

def digest {H : Type} (D : aspis_core.digest.Digest32 H) : NMP_prepare.aspis_core.digest.Digest32 H:=
 ⟨D.coremarkerCopyInst,D.digest⟩

def phase : NMP_prepare.verifier.Phase → verifier.Phase
 | .Parsed=>.Parsed | .Semantic=>.Semantic | .SemanticPart i=>.SemanticPart i
 | .Prepare=>.Prepare | .CheckpointRead=>.CheckpointRead | .Merkle i=>.Merkle i
 | .Query i=>.Query i | .QueryPart i j=>.QueryPart i j
 | .CheckpointWrite=>.CheckpointWrite | .Relation=>.Relation | .Final=>.Final

def observer (obs : Option (verifier.Phase → Result Unit)) : NMP_Emitted.Observer :=
 obs.map (fun f=>fun p=>f (phase p))

def error : NMP_prepare.verifier.Error → verifier.Error
 | .Parse=>.Parse | .Semantic=>.Semantic | .Transcript=>.Transcript | .Relation=>.Relation
 | .Merkle=>.Merkle | .Query=>.Query | .Checkpoint=>.Checkpoint | .Allocation=>.Allocation

def input {H : Type} (D : aspis_core.digest.Digest32 H)
 (pub : aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public) (proof : Slice U8)
 (h : H) (obs : Option (verifier.Phase → Result Unit))
 (g : Array aspis_core.field.wide_exact.WideExact 29#usize) : NMP_Emitted.Parent H Unit :=
 ⟨digest D,NMP_Transport.fromT9 (toT9 pub),proof,h,observer obs,
   arr NNG_PrepareCarriers087.wideBack (arr toT3 g),(),[]⟩

def output (r : NMP_Emitted.PreparedOut) :
 core.result.Result verifier.Prepared verifier.Error × Array aspis_core.field.wide_exact.WideExact 29#usize:=
 ((match r.1 with
 | .Err e=>.Err (error e)
 | .Ok p=>.Ok (fromT12 (NNG_PrepareCarriers087.prepared p))),
 arr fromT3 (arr NNG_PrepareCarriers087.wide r.2))

def call {H : Type} (env : RSL.Env) (D : aspis_core.digest.Digest32 H)
 (pub : aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public) (proof : Slice U8)
 (h : H) (obs : Option (verifier.Phase → Result Unit))
 (g : Array aspis_core.field.wide_exact.WideExact 29#usize) :=
 NMP_ResultTransport.outer output
  (NMP_Emitted.prepare (NNG_PrepareEmission087.calls env) (input D pub proof h obs g))
end AspisR1.NNG_PrepareAdapter094
