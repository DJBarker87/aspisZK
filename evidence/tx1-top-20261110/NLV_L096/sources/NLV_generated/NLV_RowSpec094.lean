import NLV_CutFold
import NLV_InitialState
import NLV_Deployed
import NLN_TX1_081
import NHS_PrepareFields
set_option autoImplicit false
noncomputable section
namespace AspisR1.NLV_Interface
open Aeneas Aeneas.Std Result AspisR1CurrentCaller
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
/-- Typed full payload observations. These must be produced from the actual
frozen heap/ABI, not manufactured from the source state. Physical interpretation
is OPEN; an address or a selected limb never substitutes for this inventory. -/
inductive Payload where
 | scratch (g : NLJ_Tx1.Scratch)
 | prepared (p : verifier.Prepared)
 | accumulator (a : verifier.Accumulator)
 | geometry (g : verifier.QueryGeometry)
 | pending (p : verifier.BatchedWeights)
 | checkpoint (b : alloc.vec.Vec U8)
structure ResourceSnapshot where
 payload : NLV.OwnedKind → Option Payload
 initialized : NLV.OwnedKind → Bool
 exclusive : NLV.OwnedKind → Bool
/-- The native observer must bind every live complete carrier, including
nested Vec buffers and the mutually borrowed weights/raw/geometry buffers. -/
def CarrierBindings (s : NLV.State) (r : ResourceSnapshot) : Prop :=
 (∀ kind, r.payload kind≠none →
   r.initialized kind=true ∧ ∃ a,s.ownership.allocations kind=some a ∧
    a.live=true ∧ a.address>0 ∧ a.initialized≤a.capacity) ∧
 (match s.core.locals with
 | .prepare g => r.payload .scratch=some (.scratch g)
 | .accumulator g p => r.payload .scratch=some (.scratch g) ∧ r.payload .prepared=some (.prepared p)
 | .markPrepare g p a | .foldedSlice g p a | .foldedCopy g p a _ |
   .foldedUnwrap g p a _ | .batch0 g p a _ | .markMerkle g p a | .geometry g p a =>
   r.payload .scratch=some (.scratch g) ∧ r.payload .prepared=some (.prepared p) ∧
   r.payload .accumulator=some (.accumulator a)
 | .pending g p a geom => r.payload .scratch=some (.scratch g) ∧ r.payload .prepared=some (.prepared p) ∧
   r.payload .accumulator=some (.accumulator a) ∧ r.payload .geometry=some (.geometry geom)
 | .query g p a geom pending => r.payload .scratch=some (.scratch g) ∧ r.payload .prepared=some (.prepared p) ∧
   r.payload .accumulator=some (.accumulator a) ∧ r.payload .geometry=some (.geometry geom) ∧
   r.payload .pending=some (.pending pending)
 | .finishPending p a pending => r.payload .prepared=some (.prepared p) ∧
   r.payload .accumulator=some (.accumulator a) ∧ r.payload .pending=some (.pending pending)
 | .checkpoint p a => r.payload .prepared=some (.prepared p) ∧ r.payload .accumulator=some (.accumulator a)
 | .markCheckpoint b | .returned b => r.payload .checkpoint=some (.checkpoint b)
 | _ => True)
/-- Raw native Result is preserved separately; its model interpretation is
not falsely identified with a returned batch Parse/Merkle error. -/
structure Observation094 where
 after : NLV.State
 raw : Result NLJ_Tx1.Out
 model : NGP_L181.Observation NLJ_Tx1.Out
 events : List NLV.Event
 terminal : Option NLJ_Tx1.Event
 resources : NLV.Event → ResourceSnapshot
abbrev Native094 := NLV.State → Observation094
/-- The bb/bc rejection transport at batch0: faithful exits retain Err, while
collapsed post-loop exits are outer fail. The SAME-code Invocation and
NativeAssociation below FIX the model outcome; this disjunction never chooses
it freely. The raw tag is retained in both cases. Every other Err keeps its
nominal tag; all successful bytes and runtime abort/div outcomes remain exact. -/
def ResultTransport (out : Observation094) : Prop :=
 out.terminal=out.events.getLast?.map (fun e=>e.kind) ∧
 match out.raw with
 | .ok (.Ok bytes) => out.model.result=ok (.Ok bytes)
 | .ok (.Err e) =>
   if out.terminal=some .batch0 then
    (e=.Parse ∨ e=.Merkle) ∧
    (out.model.result=ok (.Err e) ∨ out.model.result=fail .panic)
   else out.model.result=ok (.Err e)
 | .fail e => out.model.result=fail e
 | .div => out.model.result=div
/-- Verbatim bf own-argument clauses of CLOSED081, at the parent event's
ACTUAL proof, Prepared and folded-root values. No Result is a domain premise. -/
def BatchDomain (s : NLV.State) : Prop :=
 match s.core.locals with
 | .batch0 _ p _ folded =>
   let prepared:=Tx1Q_Carriers.prepared p
   s.core.input.proof.val.length=57607 ∧
   ∃ parsed : OraclePortCompactDraft.Parsed,
    parsed.wire=MultiproofConeCanonical.bytesOf s.core.input.proof.val ∧
    (∀ j,j<22 → prepared.queries.val[j]!.val<262144) ∧
    (∀ k : Fin 3,Port3_NativeBatchCalls.rootAt (NLL_BatchSource.roots prepared folded) k=
      AspisV8R19.SqueezeOracleBridge.encodeState (OraclePortBatchDraft.committedRoot parsed k.val))
 | _ => True
/-- The exact writer domain, including its SAME post-flush accumulator.
No independently supplied checkpoint or accepted-only child premise occurs. -/
def CheckpointDomain (s : NLV.State) : Prop :=
 match s.core.locals with
 | .checkpoint p a =>
   s.core.input.k.val=10 ∧ p.variant=.S2 ∧
   s.core.input.proof.val.length=57607 ∧ s.core.input.publicBytes.val.length=1880 ∧
   a.next.val=10 ∧ a.weights.val.length=64 ∧
   NGC_KNE_Caller.WriterDomain
    (CheckpointBytes3Namespaces.toPrepared (Tx1Q_Carriers.prepared p))
    (CheckpointBytes3Namespaces.toAccumulator (Tx1Q_Carriers.accumulator a))
 | _ => True
def ReturnedOwnership (out : Observation094) : Prop :=
 match out.raw with
 | .ok (.Ok bytes) =>
   bytes.val.length=1768 ∧
   ∃ allocated, out.after.ownership.allocations .checkpoint=some allocated ∧
    allocated.live=true ∧ allocated.bytes=bytes.val ∧
    allocated.initialized=bytes.val.length ∧ bytes.val.length≤allocated.capacity ∧
    ∀ kind,kind≠.checkpoint → out.after.ownership.allocations kind=none
 | .ok (.Err _) => ∀ kind,out.after.ownership.allocations kind=none
 | .fail _ => True
 | .div => True
/-- SAME original source arguments. Proof and public extents are explicit own-input
clauses passed to TX1:328; no physical-state predicate is a caller clause. -/
def CallerDomain (i : NLJ_Tx1.Input) : Prop :=
 i.proof.val.length=57607 ∧ i.publicBytes.val.length=1880
/-- Full-strength corrected TARGET under be/bf. It is UNPROVED. The concrete
native producer must realize every Cut, child-domain conclusion, frame and
owned cleanup fact. No empty relation or freely chosen child success can
instantiate this packet. Operations are fixed to RPx's installation. -/
def RowSpec_094 {C : Type} (missing : IDa_Deployed.Uninstalled C) (indexError : C)
 (reservation : NP6_StdModel.Reservation) (native : Native094) : Prop :=
 ∀ (i : NLJ_Tx1.Input) (frame : NLJ_Packets.Frame094), CallerDomain i →
 i.digest=NLV_Deployed.digest missing indexError reservation →
 let s:=NLV.initial i frame
 let out:=native s
 NLV.Invocation (NLV_Deployed.configuration missing indexError reservation) s.core.input.hashv
  20 s out.model.result out.model.attempted out.events out.after ∧
 ResultTransport out ∧ ReturnedOwnership out ∧
 (∀ e∈out.events,CarrierBindings e.pre (out.resources e) ∧ BatchDomain e.pre ∧ CheckpointDomain e.pre) ∧
 NGP_L181.NativeAssociation s.core.input.hashv
  (NGQ_Normalize.normalize (GExp_FirstCode.code
   (NLV_Deployed.configuration missing indexError reservation).base
   (NLV_Deployed.configuration missing indexError reservation).boundaries
   (NLV_Deployed.configuration missing indexError reservation).std
   s.core.input.hashv s.core.input.digest s.core.input.publicValue
   s.core.input.publicBytes s.core.input.proof s.core.input.k)) out.model ∧
 out.after.external=s.external ∧ out.after.core.input=s.core.input
#print CarrierBindings
#print RowSpec_094
#print ResultTransport
#print BatchDomain
#print CheckpointDomain
end AspisR1.NLV_Interface
end
