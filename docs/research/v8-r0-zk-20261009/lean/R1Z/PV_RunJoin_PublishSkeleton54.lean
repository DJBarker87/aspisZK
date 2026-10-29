import PV_RJ4IDB_OpenInputs
import R1Z.PV_RunJoin_PublishReach54
import R1Z.PV_RunJoin_OpeningImages54
import R1Z.PV_RunJoin_CoefficientsActual50
import R1Z.PV_RunJoin_CoefficientsWeight46
import R1Z.PV_RunJoin_SemanticMaterialInputs50
import R1Z.PV_RunJoin_CircleNeutralR24Prefix53
import R1Z.PV_RunJoin_CircleRawSampler52
import R1Z.ProverCommitPublish43
/-! Conditional top-down composition. Every remaining source association has
its own fixed Prop. No link is an axiom or an instance. The source phase here
starts at prove_from_semantics; installation into its native caller remains
upstream. The model publication tests the source outcome, but never reads the
source proof bytes. Thus failures are None and every successful proof must
have the full ordered model assembly. -/
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_PublishSkeleton54
open Aeneas Aeneas.Std Result ProverRwFull
open PV_RunJoin_WeightInstalled46
namespace OI := PV_RunJoin_OpeningImages54
namespace PB := ProverCommitPublish43
abbrev Bytes := List UInt8
abbrev W := aspis_core.field.wide_exact.WideExact
abbrev Q := (U32 × U32) × (U32 × U32)

def bytes (xs : List U8) : Bytes := xs.map (fun x => UInt8.ofNat x.val)
def resultBytes (r : Result (core.result.Result (alloc.vec.Vec U8) verifier.Error)) : Option Bytes :=
  match r with
  | .ok (.Ok v) => some (bytes v.val)
  | _ => none

def exceptBytes (r : Except PB.Error Bytes) : Option Bytes :=
  match r with
  | .ok b => some b
  | .error _ => none

structure Plan where
  (header semantic claim inactive root : Bytes)
  queries : List PB.QueryParts
  slots : List PB.Slot
  (offOpenings offNodes proofBytes : Nat)
  (afterstate statement proofPath statementPath : Bytes)

structure Run [ExternalTypes] where
  public1 : aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public
  hash : Slice (Slice U8) → Result (Array U8 32#usize)
  backend : prover.Backend
  sem : host_semantic.BuiltSemantics aspis_core.digest.LegacyHashFn
  salts : aspis_prover.state_only_entropy.ReservedStateOnlyAttemptSecrets ×
    aspis_core.state_only_hiding.StateOnlyHidingContext
  data : OI.Data
  plan : Plan

variable [ExternalTypes] [ExternalFuns]
def source (r : Run) := prover.prove_from_semantics r.public1 .S2 r.hash r.backend r.sem r.salts

def front (r : Run) : Bytes := r.plan.header ++ r.plan.semantic ++ r.plan.claim ++
  r.plan.inactive ++ OI.round0 r.data ++ r.plan.root ++ OI.round1 r.data ++ OI.finalBytes r.data

def assembly (r : Run) : Except PB.Error Bytes :=
  PB.assemble (.ok (front r)) r.plan.queries r.plan.slots r.plan.offNodes r.plan.proofBytes

def publication (r : Run) (proof : Bytes) : PV_RJ4IDB.PublicationInput :=
  ⟨r.plan.afterstate,proof,r.plan.statement,r.plan.proofPath,r.plan.statementPath⟩

def actual {I : Type} (runs : I → Run) (i : I) : Option Bytes := resultBytes (source (runs i))
def published {I : Type} (runs : I → Run) (i : I) : Option PV_RJ4IDB.PublicationInput :=
  match source (runs i) with
  | .ok (.Ok _) => (exceptBytes (assembly (runs i))).map (publication (runs i))
  | _ => none

/-- Neutral only: no colliding generated Types authority is imported. -/
def PV_RunJoin_Link_R24Sampler : Prop :=
  (∀ a b : Q, PV_RunJoin_CircleNeutralShape53.QC a → PV_RunJoin_CircleNeutralShape53.QC b →
    ∃ y, PV_RunJoin_CircleR72Raw52.field.r24_canonical_mul a b=ok (some y) ∧
      PV_RunJoin_CircleRawTower52.field.QM31.mul a b=ok y ∧
      PV_RunJoin_CircleNeutralShape53.QC y) ∧
  (∀ block : Array U8 32#usize, ∃ y,
    PV_RunJoin_CircleRawSampler52.shipped_sampler.qm31_sample block=ok y ∧
      PV_RunJoin_CircleNeutralShape53.QC y)

def PV_RunJoin_Link_CommonSample {I : Type} (runs : I → Run) : Prop :=
  PV_RunJoin_Link_R24Sampler → ∀ i (prepared : prover.PreparedOpening),
    prover.prepare_opening .S2 (runs i).hash (runs i).backend (runs i).sem=ok (.Ok prepared) →
    OI.Sample (runs i).data ∧
    (runs i).data.p=PV_RunJoin_SemanticMaterialInputs50.alpha (runs i).sem ∧
    (runs i).data.x0=PV_RunJoin_SemanticMaterialInputs50.x0 (runs i).sem ∧
    (runs i).data.y0=PV_RunJoin_SemanticMaterialInputs50.y0 (runs i).sem ∧
    (runs i).data.x1=PV_RunJoin_SemanticMaterialInputs50.x1 (runs i).sem ∧
    (runs i).data.y1=PV_RunJoin_SemanticMaterialInputs50.y1 (runs i).sem ∧
    ProverRwDictionaryTower.fromW (ProverCommitWideOps48.source (runs i).data.g)=prepared.gamma ∧
    ProverRwDictionaryTower.fromW (ProverCommitWideOps48.source (runs i).data.k)=prepared.kappa ∧
    ProverRwDictionaryTower.fromW (ProverCommitWideOps48.source (runs i).data.a)=prepared.alpha0

def PV_RunJoin_Link_BackendInput {I : Type} (runs : I → Run) : Prop :=
  ∀ i (prepared : prover.PreparedOpening),
    prover.prepare_opening .S2 (runs i).hash (runs i).backend (runs i).sem=ok (.Ok prepared) →
    OI.Coefficients (runs i).data ∧
    alloc.vec.Vec.deref (runs i).backend.messages=PV_RunJoin_CoefficientsWeight46.messages
      (fun l j => ProverRwDictionaryTower.fromW (ProverCommitNativeOps47.embedded ((runs i).data.c l j))) ∧
    (runs i).backend.messages.length=29

def CoefficientCaller (r : Run) : Prop := ∃ coeff,
  prover.opening_coefficients .S2 (alloc.vec.Vec.deref r.backend.messages)=ok coeff ∧
  coeff.val=r.backend.messages.val.map PV_RunJoin_CoefficientActualCell50.permuted ∧
  coeff.length=r.backend.messages.length

/-- The source association of front fields; the three opening images come
from the already proved coefficient/weight/fold composition. -/
def Fields (r : Run) (p : prover.Publication) : Prop :=
  bytes p.c0bytes.val=OI.round0 r.data ∧ bytes p.c1bytes.val=OI.round1 r.data ∧
  bytes p.fbytes.val=OI.finalBytes r.data ∧
  bytes p.semantic_bytes.val=r.plan.semantic ∧ bytes p.y1.val=r.plan.claim ∧
  bytes p.root.val=r.plan.root ∧
  (∃ ib, aspis_core.field.wide_exact.WideExact.to_le_bytes p.inactive=ok ib ∧
    bytes ib.val=r.plan.inactive)

def PV_RunJoin_Link_FinishContext {I : Type} (runs : I → Run) : Prop :=
  ∀ i (prepared : prover.PreparedOpening) (salts : host_commitment.PrivateSalts)
    (p : prover.Publication) (hc : OI.Coefficients (runs i).data),
    prover.prepare_opening .S2 (runs i).hash (runs i).backend (runs i).sem=ok (.Ok prepared) →
    prover.derive_private_salts (runs i).salts.1 (runs i).salts.2 (runs i).hash 114#u8=ok (.Ok salts) →
    prover.finish_opening .S2 (runs i).hash prepared salts=ok (.Ok p) →
    CoefficientCaller (runs i) → OI.Images (runs i).data hc → Fields (runs i) p

def PV_RunJoin_Link_QueryAppend {I : Type} (runs : I → Run) : Prop :=
  ∀ i (p : prover.Publication), Fields (runs i) p →
  (runs i).plan.queries.length=22 ∧ ∀ out cc1 cc2,
    p.backend.c1=some cc1 → p.backend.c2=some cc2 → out.length=(runs i).plan.offOpenings →
    ∃ next, prover.append_query_openings out cc1 cc2 p.queries
      (alloc.vec.Vec.deref p.folded_word) p.folded_salts=ok next ∧
      bytes next.val=PB.queries (runs i).plan.queries (bytes out.val)

def indices (queries : Array U32 22#usize) (begin1 end1 : Nat) (folded : Bool) : List Nat :=
  (((queries.val.drop begin1).take (end1-begin1)).map
    (fun q => if folded then q.val/4 else q.val)).mergeSort (· ≤ ·) |>.eraseDups

def PV_RunJoin_Link_NodeAppend {I : Type} (runs : I → Run) : Prop :=
  ∀ i (p : prover.Publication), Fields (runs i) p →
  (runs i).plan.slots.length=6 ∧
  (∀ begin1 end1 folded, begin1.val≤end1.val → end1.val≤22 →
    ∃ idx, prover.publication_indices p.queries begin1 end1 folded=ok idx ∧
      idx.val.map UScalar.val=indices p.queries begin1.val end1.val folded) ∧
  (∀ out cc1 cc2, p.backend.c1=some cc1 → p.backend.c2=some cc2 →
    out.length=(runs i).plan.offNodes →
    resultBytes (prover.append_node_slots out cc1 cc2 p.tree p.queries)=
      exceptBytes (PB.slots (runs i).plan.slots (bytes out.val)))

/-- Local serializer ordering, not the complete actual-run conclusion. -/
def PV_RunJoin_Link_PublishOrder {I : Type} (runs : I → Run) : Prop :=
  PV_RunJoin_Link_QueryAppend runs → PV_RunJoin_Link_NodeAppend runs →
  ∀ i (p : prover.Publication) (proof : alloc.vec.Vec U8), Fields (runs i) p →
    prover.publish_compact .S2 p=ok (.Ok proof) →
    PB.assembleLoop (.ok (front (runs i))) (runs i).plan.queries (runs i).plan.slots
      (runs i).plan.offNodes (runs i).plan.proofBytes=.ok (bytes proof.val)

theorem complete {I : Type} (base : ExternalTypes) (heap : Heap) (box : Box)
    (ops : @ExternalFuns (types base)) (runs : I → @Run (types base))
    (r24 : PV_RunJoin_Link_R24Sampler)
    (common : @PV_RunJoin_Link_CommonSample (types base) (selected base heap box ops) I runs)
    (backend : @PV_RunJoin_Link_BackendInput (types base) (selected base heap box ops) I runs)
    (finish : @PV_RunJoin_Link_FinishContext (types base) (selected base heap box ops) I runs)
    (query : @PV_RunJoin_Link_QueryAppend (types base) (selected base heap box ops) I runs)
    (node : @PV_RunJoin_Link_NodeAppend (types base) (selected base heap box ops) I runs)
    (ordering : @PV_RunJoin_Link_PublishOrder (types base) (selected base heap box ops) I runs) :
    PV_RJ4IDB.OpenInputs.RUNJOIN_PUBLISH_COMPACT
      (@actual (types base) (selected base heap box ops) I runs)
      (@published (types base) (selected base heap box ops) I runs) := by
  letI : ExternalTypes := types base
  letI : ExternalFuns := selected base heap box ops
  intro i
  cases hs : source (runs i) with
  | fail e => simp only [actual,published,hs,resultBytes]
  | div => simp only [actual,published,hs,resultBytes]
  | ok result =>
    cases result with
    | Err e => simp only [actual,published,hs,resultBytes]
    | Ok proof =>
      obtain ⟨prepared,salts,p,hp,hsalts,hf,hpub⟩ := PV_RunJoin_PublishReach54.complete
        (runs i).public1 .S2 (runs i).hash (runs i).backend (runs i).sem (runs i).salts proof hs
      obtain ⟨hc,hinput,hlen⟩ := backend i prepared hp
      have sample := (common r24 i prepared hp).1
      have images := OI.complete (runs i).data hc sample
      have small : (alloc.vec.Vec.deref (runs i).backend.messages).length≤14336 := by
        change (runs i).backend.messages.length≤14336
        rw [hlen]; omega
      have coeff : CoefficientCaller (runs i) :=
        PV_RunJoin_CoefficientsActual50.complete base heap box ops
          (alloc.vec.Vec.deref (runs i).backend.messages) small
      have fields := finish i prepared salts p hc hp hsalts hf coeff images
      have assembled := ordering query node i p proof fields hpub
      rw [PB.assemble_loop] at assembled
      have ha : assembly (runs i)=.ok (bytes proof.val) := assembled
      simp only [actual,published,hs,resultBytes,ha,exceptBytes,Option.map_some,publication]

#print axioms bytes
#print axioms resultBytes
#print axioms exceptBytes
#print axioms source
#print axioms front
#print axioms assembly
#print axioms publication
#print axioms actual
#print axioms published
#print axioms PV_RunJoin_Link_R24Sampler
#print axioms PV_RunJoin_Link_CommonSample
#print axioms PV_RunJoin_Link_BackendInput
#print axioms CoefficientCaller
#print axioms Fields
#print axioms PV_RunJoin_Link_FinishContext
#print axioms PV_RunJoin_Link_QueryAppend
#print axioms indices
#print axioms PV_RunJoin_Link_NodeAppend
#print axioms PV_RunJoin_Link_PublishOrder
#print axioms complete
end R1Z.PV_RunJoin_PublishSkeleton54
