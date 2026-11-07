import NNG_Error328
import NNG_TypedEvents
import NNG_SourceStep136
set_option autoImplicit false
noncomputable section
namespace AspisR1.NNG_Tree328
open Aeneas Aeneas.Std Result NMT_first NMT_CallTree NNG_Carriers328 NNG_Native328
abbrev Observer := Option (aspis_r1_cost_probe.verifier.Phase → Result Unit)
abbrev ChildArgs := aspis_core.digest.Digest32 Unit × Public × Slice U8 × Slice U8 × Usize × Unit × Observer

def childArgs (a : Args) (env : RSL.Env) : ChildArgs :=
 (SolanaDigest.Insts.Aspis_coreDigestDigest32 call4 (call5 env),a.public_,a.publicBytes,a.proof,a.k,(),none)
def childEvents (env : RSL.Env) (a : ChildArgs) : List RSL.Event :=
 (NNG_ProducerFull094.producer (args ⟨a.2.1,a.2.2.1,a.2.2.2.1,a.2.2.2.2.1⟩) none env).events

def events (env : RSL.Env) (event : NMT_CallTree.Event) : List RSL.Event :=
 NNG_TypedEvents.select "TX1:094/tx1" (childEvents env) event ++
 NNG_TypedEvents.select "lib.rs::error" NNG_Error328.events event

def child (a : Args) (env : RSL.Env) : Code (core.result.Result (alloc.vec.Vec U8) NNG_Carriers328.Error) :=
 invoke "TX1:094/tx1" (childArgs a env)
  (call1 env (SolanaDigest.Insts.Aspis_coreDigestDigest32 call4 (call5 env))
   a.public_ a.publicBytes a.proof a.k () none)
def tail (r : core.result.Result (alloc.vec.Vec U8) NNG_Carriers328.Error) : Code (core.result.Result (alloc.vec.Vec U8) solana_program_error.ProgramError) :=
 match r with
 | .Ok bytes=>pure (.Ok bytes)
 | .Err e=>do let pe ← invoke "lib.rs::error" e (call6 e);pure (.Err pe)
def tree (a : Args) (env : RSL.Env) := NMT_CallTree.bind (child a env) tail

theorem child_call {Reply : Type} (env : RSL.Env) (a : ChildArgs) (r : Result Reply) :
 events env (.call "TX1:094/tx1" a r)=childEvents env a := by
 simp [events,NNG_TypedEvents.select]
#print axioms child_call
theorem error_call {Reply : Type} (env : RSL.Env) (e : NNG_Carriers328.Error) (r : Result Reply) :
 events env (.call "lib.rs::error" e r)=NNG_Error328.events e := by
 simp [events,NNG_TypedEvents.select]
#print axioms error_call

theorem source (a : Args) (env : RSL.Env) : erase (tree a env)=NNG_Native328.body a env := by
 rw [NNG_Native328.source]
 unfold tree child
 rw [erase_bind,erase_invoke]
 apply result_congr
 intro r
 cases r with
 | Ok bytes=>rfl
 | Err e=>
  change erase (NMT_CallTree.bind (invoke "lib.rs::error" e (call6 e)) (fun pe=>pure (.Err pe)))=_
  rw [erase_bind,erase_invoke]
  rfl
#print axioms source
end AspisR1.NNG_Tree328
