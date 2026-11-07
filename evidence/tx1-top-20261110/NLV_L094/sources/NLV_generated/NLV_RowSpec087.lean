import NLR_RowSpec087
import NLV_State
set_option autoImplicit false
noncomputable section
namespace AspisR1.NLV_Resource087
open Aeneas Aeneas.Std Result AspisR1CurrentCaller
open AspisR1PublicPreparation
abbrev Scratch := NLJ_Prepare.Scratch
abbrev Local := NLJ_Prepare.Local Unit
structure View where
 address : Nat
 offset : Nat
 length : Nat
 values : List U8
 live : Bool
/-- All fields denote observations of ONE physical invocation. They must be
realized by a reviewed P6 heap/ABI interpretation, never fabricated from a
source value or inferred from an address. This type is an OPEN obligation. -/
structure State where
 sourceState : NLJ_Prepare.State Unit
 external : NLR_Interface.ExternalFrame
 scratchAddress : Nat
 scratchValue : Scratch
 scratchExclusive : Bool
 logical : Option NLV.Allocation
 semanticOwner : Option NLV.Allocation
 semanticValue : Option (r1_semantic.Verified Unit)
 preparedOwner : Option NLV.Allocation
 preparedValue : Option verifier.Prepared
 semanticView : Option View
 y1View : Option View
/-- Source-owned buffer at each exact occurrence, including disjoint rebuild. -/
def logicalValue : Local → Option (List U8)
 | .allocate => none
 | .split _ logical => some logical.val
 | .semanticRange _ semantic y1 _ _ => some (semantic.val++y1.val)
 | .expandSemantic _ _ semantic y1 _ _ _ => some (semantic.val++y1.val)
 | .valueRange _ _ semantic y1 _ _ => some (semantic.val++y1.val)
 | .expandValues _ semantic y1 _ _ _ => some (semantic.val++y1.val)
 | .rebuild _ semantic y1 _ _ => some (semantic.val++y1.val)
 | .view logical _ _ => some logical.val
 | .semantic logical _ => some logical.val
 | .mapSemantic logical _ _ => some logical.val
 | .mark logical _ _ => some logical.val
 | .constructor logical _ _ => some logical.val
def viewValues : Local → Option (Slice U8 × Slice U8)
 | .semanticRange _ semantic y1 _ _ => some (semantic,y1)
 | .expandSemantic _ _ semantic y1 _ _ _ => some (semantic,y1)
 | .valueRange _ _ semantic y1 _ _ => some (semantic,y1)
 | .expandValues _ semantic y1 _ _ _ => some (semantic,y1)
 | .rebuild _ semantic y1 _ _ => some (semantic,y1)
 | .view _ semantic y1 => some (semantic,y1)
 | .semantic _ v => some (v.semantic,v.y1)
 | .mapSemantic _ v _ => some (v.semantic,v.y1)
 | .mark _ v _ => some (v.semantic,v.y1)
 | .constructor _ v _ => some (v.semantic,v.y1)
 | _ => none
def semanticValue : Local → Option (r1_semantic.Verified Unit)
 | .mapSemantic _ _ (.Ok sem) => some sem
 | .mark _ _ sem => some sem
 | .constructor _ _ sem => some sem
 | _ => none
def allocationLive (a : NLV.Allocation) : Prop :=
 a.live=true ∧ a.address>0 ∧ a.initialized=a.bytes.length ∧ a.bytes.length≤a.capacity
def viewBound (a : NLV.Allocation) (v : View) : Prop :=
 v.live=true ∧ v.address=a.address+v.offset ∧ v.offset+v.length≤a.bytes.length ∧
 v.values=(a.bytes.drop v.offset).take v.length
/-- Values, initialized extents, original owners, disjoint views and semantic
claims/Verified payload are all required. Pointer equality alone proves none. -/
def Bindings (s : State) : Prop :=
 (match logicalValue s.sourceState.locals with
 | none => s.logical=none
 | some bytes => ∃ a,s.logical=some a ∧ allocationLive a ∧ a.bytes=bytes) ∧
 (match viewValues s.sourceState.locals with
 | none => True
 | some pair => ∃ a sv yv,s.logical=some a ∧ s.semanticView=some sv ∧ s.y1View=some yv ∧
   viewBound a sv ∧ viewBound a yv ∧ sv.offset=0 ∧ yv.offset=pair.1.val.length ∧
   sv.length=pair.1.val.length ∧ yv.length=pair.2.val.length ∧
   sv.values=pair.1.val ∧ yv.values=pair.2.val ∧ sv.offset+sv.length≤yv.offset) ∧
 (match semanticValue s.sourceState.locals with
 | none => True
 | some sem => s.semanticValue=some sem ∧ ∃ owner,s.semanticOwner=some owner ∧ allocationLive owner)
structure Event where
 pre : State
 kind : NLJ_Prepare.Event
def event (s : State) : Event := ⟨s,NLJ_Prepare.event s.sourceState⟩
/-- Required complete native cut transcription. Source flow and physical
observations are BOTH conclusions of the future native proof; this is not an
admitted producer and must never be inserted as an endpoint root premise. -/
structure Cut (cfg : NLJ_Prepare.Configuration) (s after : State)
 (reply : Result (NLJ_Prepare.Post Unit)) (log : PreparedHashCode.Log) : Prop where
 binding : Bindings s
 inputs : after.sourceState.input=s.sourceState.input
 readonly : after.external=s.external
 scratchOwner : after.scratchAddress=s.scratchAddress
 flow : PreparedHashCode.run (NLJ_Prepare.step cfg s.sourceState)=(log,reply)
 nextBinding : match reply with | .ok (.inr _) => Bindings after | _ => True
/-- All cuts share the same full state; terminal Err/fail/div have no suffix. -/
inductive Invocation (cfg : NLJ_Prepare.Configuration) :
 Nat → State → Result NLJ_Prepare.Out → PreparedHashCode.Log → List Event → State → Prop where
 | returned {n : Nat} {s after : State} {out : NLJ_Prepare.Out} {log : PreparedHashCode.Log}
   (head : Cut cfg s after (ok (.inl out)) log) :
   Invocation cfg (n+1) s (ok out) log [event s] after
 | next {n : Nat} {s middle last : State} {out : Result NLJ_Prepare.Out}
   {log suffix : PreparedHashCode.Log} {events : List Event}
   (head : Cut cfg s middle (ok (.inr middle.sourceState)) log)
   (tail : Invocation cfg n middle out suffix events last) :
   Invocation cfg (n+1) s out (log++suffix) (event s::events) last
 | fail {n : Nat} {s after : State} {error : Error} {log : PreparedHashCode.Log}
   (head : Cut cfg s after (fail error) log) :
   Invocation cfg (n+1) s (fail error) log [event s] after
 | div {n : Nat} {s after : State} {log : PreparedHashCode.Log}
   (head : Cut cfg s after div log) :
   Invocation cfg (n+1) s div log [event s] after
structure Observation where
 value : NLR_Interface.Observation087
 after : State
 events : List Event
abbrev Native := State → Observation
def Admission (s : State) : Prop :=
 s.sourceState.locals=.allocate ∧ s.scratchValue=s.sourceState.input.scratch ∧
 s.scratchAddress>0 ∧ s.scratchAddress%4=0 ∧ s.scratchExclusive=true ∧
 s.logical=none ∧ s.semanticOwner=none ∧ s.preparedOwner=none ∧
 s.semanticView=none ∧ s.y1View=none
def Returned (reply : Result NLJ_Prepare.Out) (after : State) : Prop :=
 match reply with
 | .ok (r,scratch) =>
   after.scratchValue=scratch ∧ after.scratchExclusive=false ∧
   after.logical=none ∧ after.semanticOwner=none ∧ after.semanticView=none ∧ after.y1View=none ∧
   match r with
   | .Err _ => after.preparedOwner=none ∧ after.preparedValue=none
   | .Ok p => after.preparedValue=some p ∧ ∃ owner,after.preparedOwner=some owner ∧ allocationLive owner
 | .fail _ => True
 | .div => True
/-- FULL087 TARGET, strictly extending the sibling's explicitly weaker
source/value schema. Native is the reviewed frozen producer, never a freely
chosen model function. Physical admission is existing P6/runtime/allocator
interpretation, not a new bf caller-domain or trust item. No proof is supplied.
A future root fixes cfg to the headline, and discharges every caller clause. -/
def RowSpec_087 (cfg : NLJ_Prepare.Configuration)
 (valueNative : NLR_Interface.Native087) (native : Native) : Prop :=
 NLR_Interface.RowSpec_087 cfg valueNative ∧
 ∀ s : State, Admission s →
 let out:=native s
 out.value=valueNative s.sourceState.input s.external ∧
 out.value.afterInput=s.sourceState.input ∧ out.value.afterFrame=s.external ∧
 Invocation cfg 12 s out.value.reply out.value.log out.events out.after ∧
 Returned out.value.reply out.after ∧
 out.after.external=s.external ∧ out.after.scratchAddress=s.scratchAddress
/-- Source projection only; no resource/native closure follows from this lemma. -/
theorem source_projection (cfg : NLJ_Prepare.Configuration)
 (valueNative : NLR_Interface.Native087) (native : Native)
 (full : RowSpec_087 cfg valueNative native) : NLR_Interface.RowSpec_087 cfg valueNative := full.1
#print axioms source_projection
#print RowSpec_087
#print Bindings
#print Returned
end AspisR1.NLV_Resource087
end
