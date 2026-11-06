import NLV_CutFold
import NLV_Deployed
import NLN_TX1_081
import NHS_PrepareFields
set_option autoImplicit false
noncomputable section
namespace AspisR1.NLV_Interface
open Aeneas Aeneas.Std Result AspisR1CurrentCaller
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
/-- Raw native Result is preserved separately; its model interpretation is
not falsely identified with a returned batch Parse/Merkle error. -/
structure Observation094 where
 after : NLV.State
 raw : Result NLJ_Tx1.Out
 model : NGP_L181.Observation NLJ_Tx1.Out
 events : List NLV.Event
 terminal : Option NLJ_Tx1.Event
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
/-- SAME original source arguments. Public extent is the explicit own-input
clause passed to TX1:328; proof extent is derived after the actual parser. -/
def CallerDomain (s : NLV.State) : Prop :=
 NLV.InputAdmission s ∧ s.core.locals=.guard ∧
 s.core.input.publicBytes.val.length=1880 ∧
 (∀ kind,s.ownership.allocations kind=none)
/-- Full-strength corrected TARGET under be/bf. It is UNPROVED. The concrete
native producer must realize every Cut, child-domain conclusion, frame and
owned cleanup fact. No empty relation or freely chosen child success can
instantiate this packet. Operations are fixed to RPx's installation. -/
def RowSpec_094 {C : Type} (missing : IDa_Deployed.Uninstalled C) (indexError : C)
 (reservation : NP6_StdModel.Reservation) (native : Native094) : Prop :=
 ∀ s : NLV.State, CallerDomain s →
 s.core.input.digest=NLV_Deployed.digest missing indexError reservation →
 let out:=native s
 NLV.Invocation (NLV_Deployed.configuration missing indexError reservation) s.core.input.hashv
  20 s out.model.result out.model.attempted out.events out.after ∧
 ResultTransport out ∧ ReturnedOwnership out ∧
 (∀ e∈out.events,BatchDomain e.pre ∧ CheckpointDomain e.pre) ∧
 NGP_L181.NativeAssociation s.core.input.hashv
  (NGQ_Normalize.normalize (GExp_FirstCode.code
   (NLV_Deployed.configuration missing indexError reservation).base
   (NLV_Deployed.configuration missing indexError reservation).boundaries
   (NLV_Deployed.configuration missing indexError reservation).std
   s.core.input.hashv s.core.input.digest s.core.input.publicValue
   s.core.input.publicBytes s.core.input.proof s.core.input.k)) out.model ∧
 out.after.external=s.external ∧ out.after.core.input=s.core.input
#print RowSpec_094
#print ResultTransport
#print BatchDomain
#print CheckpointDomain
end AspisR1.NLV_Interface
end
