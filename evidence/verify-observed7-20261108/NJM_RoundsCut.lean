import NJM_RoundsTransport
set_option autoImplicit false
noncomputable section
namespace AspisR1.NJM_RoundsCut
open Aeneas Aeneas.Std Result AspisR1PublicPreparation NIX_CertificateFrames NJG_NativeCuts NJG_RoundsCode
open PreparedHashCode (run)

/-- Universal native G observations. This contains only the original
K016–019 cut outputs, no protocol operation, child implementation or child law. -/
structure Observations where
 post : RoundsPre → RoundOutput × Nat
 args : RoundsPre → Fin 10 → Fin 32 → Fin 4 → RoundsLog

/-- Exact reviewed NJG K016–019 transcriptions, universally quantified over
oracle replies; the caller substitutes the CLOSED133 reply below. -/
def Cut (native : Observations) : Prop :=
 (∀ s k z limb,roundsArgs {s with count:=0} k z limb (native.args s k z limb)) ∧
 (∀ s k z limb,roundsResult {s with count:=0} k z limb (native.post s).1 (native.post s).2)

def inputs {H : Type} (token frame : Nat) (r : Usize) (bound : r.val<10)
 (carry : Carry H) (reply : Output H) : RoundsPre where
 prefixToken:=token
 round:=⟨r.val,bound⟩
 alpha:=carry.2.1
 running:=carry.1
 state:=carry.2.2.state
 next:=carry.2.2.next_row
 reply:=NJM_RoundsTransport.lower reply
 count:=0
 frame:=frame

/-- The parent G after substituting the SAME complete CLOSED child Result.
Outer child aborts are terminal prefixes and do not fabricate native returns. -/
def step {H : Type} (native : Observations) (token frame : Nat)
 (D : aspis_core.Digest32 H) (pre : r1_wire.Prefix) (r : Usize) (bound : r.val<10)
 (carry : Carry H) : PreparedHashCode.Log × Result (Output H) :=
 let child:=run (S1SemanticCode.roundStep NJM_RoundJoin.R D pre carry.2.2 carry.2.1 carry.1 r)
 match child.2 with
 | .fail e=>(child.1,.fail e)
 | .div=>(child.1,.div)
 | .ok reply=>
   let post:=native.post (inputs token frame r bound carry reply)
   (child.1,ok (NJM_RoundsTransport.raise carry.2.2.hash post.1))

/-- Native-to-source direction of(aq)(5): instantiate the universally
certified G with the concrete133 result at precisely the original carry.
No inverse log association, endpoint equality, or child-success hypothesis. -/
theorem source {H : Type} (native : Observations) (certificate : Cut native) (token frame : Nat)
 (D : aspis_core.Digest32 H) (pre : r1_wire.Prefix) (r : Usize) (bound : r.val<10)
 (carry : Carry H) :
 step native token frame D pre r bound carry=
 run (S1SemanticCode.roundStep NJM_RoundJoin.R D pre carry.2.2 carry.2.1 carry.1 r) := by
 unfold step
 generalize call : run (S1SemanticCode.roundStep NJM_RoundJoin.R D pre carry.2.2 carry.2.1 carry.1 r)=child
 rcases child with ⟨log,reply⟩
 cases reply with
 | fail e=>rfl
 | div=>rfl
 | ok reply=>
   let s:=inputs token frame r bound carry reply
   have post:=NJM_RoundsNative.step s (native.post s).1 (native.post s).2 (certificate.2 s)
   have childCall : (run (S1SemanticCode.roundStep NJM_RoundJoin.R D pre carry.2.2 carry.2.1 carry.1 r)).2=ok reply := congrArg Prod.snd call
   have transport:=NJM_RoundsTransport.roundtrip carry.2.2.hash reply
    (NJM_RoundsTransport.source_frame D pre carry r bound reply childCall)
   change (log,ok (NJM_RoundsTransport.raise carry.2.2.hash (native.post s).1))=(log,ok reply)
   rw [post.1]
   exact congrArg (fun out=>(log,ok out)) transport

/-- Every native argument window is the SAME carry/thread as the child call
used by source; all local frame/counter effects are the certified originals. -/
theorem arguments {H : Type} (native : Observations) (certificate : Cut native) (token frame : Nat)
 (r : Usize) (bound : r.val<10) (carry : Carry H) (reply : Output H)
 (k : Fin 10) (z : Fin 32) (limb : Fin 4) :
 let log:=native.args (inputs token frame r bound carry reply) k z limb
 log.prefixToken=token ∧ log.round=r.val ∧
 log.alphaWord=word (cell carry.2.1 k) limb ∧ log.runningWord=word carry.1 limb ∧
 log.stateByte=cell carry.2.2.state z ∧ log.next=carry.2.2.next_row ∧ log.count=1 ∧ log.frame=frame :=
 NJM_RoundsNative.args _ k z limb _ (certificate.1 _ k z limb)

#print axioms source
#print axioms arguments
end AspisR1.NJM_RoundsCut
end
