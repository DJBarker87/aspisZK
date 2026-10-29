import R1Z.PV_RunJoin_LinkR24Discharged54
import R1Z.PV_RunJoin_NativeControl55
import R1Z.PV_RunJoin_SourceSuccessVariant55
import R1Z.PV_RunJoin_PublicationSuccess55
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_NativeCallback55
open Aeneas Aeneas.Std Result ProverRwFull PV_RunJoin_WeightInstalled46
open PV_RunJoin_PublishSkeleton54 PV_RunJoin_NativeControl55 (Phase)
open PV_RunJoin_ResultRelation55
attribute [local irreducible] prover.prove_from_semantics

def runOf [ExternalTypes] (data : Phase → PV_RunJoin_OpeningImages54.Data) (plans : Phase → Plan)
    (p : Phase) : Run := ⟨p.public1,p.hash,p.backend,p.sem,p.salts,data p,plans p⟩
def decode (proof : alloc.vec.Vec U8) := bytes proof.val

theorem source_s2 [ExternalTypes] [ExternalFuns]
    (data : Phase → PV_RunJoin_OpeningImages54.Data) (plans : Phase → Plan) (p : Phase) :
    PV_RunJoin_PublishSkeleton54.source (runOf data plans p)=
      prover.prove_from_semantics p.public1 .S2 p.hash p.backend p.sem p.salts := rfl

def model [ExternalTypes] [ExternalFuns]
    (data : Phase → PV_RunJoin_OpeningImages54.Data) (plans : Phase → Plan) (p : Phase) :=
  PV_RunJoin_PublicationResult55.install verifier.Error.Semantic (PV_RunJoin_NativeControl55.source p)
    (published (runOf data plans) p)

theorem complete (base : ExternalTypes) (heap : Heap) (box : Box)
    (ops : @ExternalFuns (types base))
    (data : @Phase (types base) → PV_RunJoin_OpeningImages54.Data)
    (plans : @Phase (types base) → Plan)
    (common : @PV_RunJoin_Link_CommonSample (types base) (selected base heap box ops) (@Phase (types base)) (runOf data plans))
    (backend : @PV_RunJoin_Link_BackendInput (types base) (selected base heap box ops) (@Phase (types base)) (runOf data plans))
    (finish : @PV_RunJoin_Link_FinishContext (types base) (selected base heap box ops) (@Phase (types base)) (runOf data plans))
    (query : @PV_RunJoin_Link_QueryAppend (types base) (selected base heap box ops) (@Phase (types base)) (runOf data plans))
    (node : @PV_RunJoin_Link_NodeAppend (types base) (selected base heap box ops) (@Phase (types base)) (runOf data plans))
    (ordering : @PV_RunJoin_Link_PublishOrder (types base) (selected base heap box ops) (@Phase (types base)) (runOf data plans))
    (p : @Phase (types base)) :
    Rel (CoreRel (fun proof pub => decode proof=PV_RJ4IDB.PublicationInput.publish_compact pub))
      (@PV_RunJoin_NativeControl55.source (types base) (selected base heap box ops) p)
      (@model (types base) (selected base heap box ops) data plans p) := by
  letI : ExternalTypes := types base
  letI : ExternalFuns := selected base heap box ops
  have typed := PV_RunJoin_LinkR24Discharged54.publication base heap box ops (runOf data plans)
    common backend finish query node ordering
  unfold model
  apply PV_RunJoin_PublicationSuccess55.complete decode PV_RJ4IDB.PublicationInput.publish_compact verifier.Error.Semantic
  intro proof success
  change prover.prove_from_semantics p.public1 p.variant p.hash p.backend p.sem p.salts=ok (.Ok proof) at success
  have hv := PV_RunJoin_SourceSuccessVariant55.complete p.public1 p.variant p.hash p.backend p.sem p.salts proof success
  have hs : PV_RunJoin_PublishSkeleton54.source (runOf data plans p)=ok (.Ok proof) := by
    rw [source_s2]
    simpa only [hv] using success
  have ht := typed p
  change resultBytes (PV_RunJoin_PublishSkeleton54.source (runOf data plans p))=_ at ht
  rw [hs] at ht
  exact ht
#print axioms runOf
#print axioms decode
#print axioms source_s2
#print axioms model
#print axioms complete
end R1Z.PV_RunJoin_NativeCallback55
