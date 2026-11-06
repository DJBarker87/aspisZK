import NKV_ProducerDomain
import NJV_TX1
set_option autoImplicit false
noncomputable section
namespace NKV_VerifyInvocation
open Aeneas Aeneas.Std Result AspisR1Stage2 AspisR1 MultiproofConeRef
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps
open MultiproofConePhysicalTransport

/-- Native child result, BOTH complete returned arrays, and identical ordered
query history. Byte domain is explicit; no verdict/success hypothesis. -/
theorem returning (H : Bytes → State) (root : Array U8 32#usize) (physical : Slice U8)
 (idx : NKV_StepErasure.Indices) (val : NKV_StepErasure.Values) (n : Usize)
 (bytes : physical.val.length≤9216)
 (events : List (NJP_RowModel.Request × NJP_RowModel.Digest)) (out : Bool × NJP_RowModel.Scratch)
 (native : NJV_NativeEntry.Invocation (NJP_RequestTransport.hash (rawOracle H))
   root physical (NJV_EntryABI.initial idx val n) events out) :
 ((eval H (NJV_TX2Returning.endpoint root physical idx val n)).1,
   (NKV_ConcreteChildren.ops H).op10 (NKV_ConcreteChildren.digest H) () .Two root idx val n physical)=
 (NJV_AdoptedObservation.history events,
   ok (out.1,(NJP_ScratchCarrier.emitted out.2).idx,(NJP_ScratchCarrier.emitted out.2).val)) := by
 have packet:=(NJV_TX2.TX2_093 H root physical idx val n bytes events out native).1
 have history:=congrArg Prod.fst packet
 have answer:=Result.ok.inj (congrArg Prod.snd packet)
 have rebuilt:=congrArg (fun x : Bool × NJP_RowModel.Scratch =>
   (x.1,(NJP_ScratchCarrier.emitted x.2).idx,(NJP_ScratchCarrier.emitted x.2).val)) answer
 simp only [NJP_CohortReturning.answer,NJP_ScratchCarrier.roundtrip] at rebuilt
 change (_,ok _)=_
 rw [history,rebuilt]

/-- The stronger TX2 gate is derived from this exact accepted intermediate
producer, not an independently selected scratch or a false <=10 claim. -/
theorem tx2 (H : Bytes → State) (p : OraclePortCompactDraft.Parsed)
 (q : Fin 22 → Fin 262144) (batch kind : Nat) (before after : reference.Scratch) (slot : Slice U8)
 (empty : before.n.val=0)
 (accepted : (NKV_LeafBuild.build H p q kind (OraclePortFrozenOrder.sortedPositions q batch kind) before).2=ok (true,after))
 (fits : 32*OraclePortFrozenOrder.nodeCount 18 (NJV_UnitDomain.keys after)≤slot.val.length)
 (root : Array U8 32#usize)
 (events : List (NJP_RowModel.Request × NJP_RowModel.Digest)) (out : Bool × NJP_RowModel.Scratch)
 (native : NJV_NativeEntry.Invocation (NJP_RequestTransport.hash (rawOracle H)) root
   (MultiproofConeSlotTail.prefixNodes slot (OraclePortFrozenOrder.nodeCount 18 (NJV_UnitDomain.keys after)))
   (NJV_EntryABI.initial after.idx after.val after.n) events out) :
 let physical:=MultiproofConeSlotTail.prefixNodes slot (OraclePortFrozenOrder.nodeCount 18 (NJV_UnitDomain.keys after))
 ((eval H (NJV_TX2Returning.endpoint root physical after.idx after.val after.n)).1,
   (NKV_ConcreteChildren.ops H).op10 (NKV_ConcreteChildren.digest H) () .Two root after.idx after.val after.n physical)=
 (NJV_AdoptedObservation.history events,
   ok (out.1,(NJP_ScratchCarrier.emitted out.2).idx,(NJP_ScratchCarrier.emitted out.2).val)) :=
 returning H root _ after.idx after.val after.n
   (NKV_ProducerDomain.tx2_bytes H p q batch kind before after slot empty accepted fits) events out native

set_option pp.proofs false
#print returning
#print tx2
#print axioms returning
#print axioms tx2
end NKV_VerifyInvocation
end
