import NMV_G2
import NMV_G2State
set_option autoImplicit false
namespace NMV_FullState
open RSL NMV_RslLaws

/-- Physical adapter payload. `Allocator` is instantiated with the FULL
runtime allocator carrier, not a Boolean or a projected allocation counter.
Its internals are outside the row obligation under (bl)(3). -/
structure World (Allocator : Type) where
 sdk : SdkState
 allocator : Allocator

/-- Complete returning state; stopped executions have only a prefix.
No post-abort SDK or allocator world exists in this carrier. -/
inductive End (Allocator A : Type) where
 | returned (reply : A) (post : World Allocator)
 | aborted
 | diverged

structure Observation (Allocator A : Type) where
 ending : End Allocator A
 events : List Event

def project {Allocator A : Type} (o : Observation Allocator A) : Obs (A × SdkState) :=
 ⟨match o.ending with
  | .returned r post => .ret (r,post.sdk)
  | .aborted => .abort
  | .diverged => .diverge, o.events⟩

/-- Full allocator argument/result is retained for A3/A4. This is exactly
RSL RowSpec_240 on each allocator instance; it adds no allocator equality,
Root0 assumption, or post-abort state. -/
def Packet240 {Allocator : Type} (L : PoolLib) (D : DeployedIds) (V : TX2_241.V2Lib)
 (impl : TX2_240.Args → World Allocator → Env → Observation Allocator (Except ProgramError Unit)) : Prop :=
 ∀ allocator, TX2_240.RowSpec_240 L D V (fun a sdk env => project (impl a ⟨sdk,allocator⟩ env))

def Packet344 {Allocator : Type} (V : VLib) (P : PreparedNew V) (C : TX1_345.S1Lib V)
 (impl : TX1_344.Args → World Allocator → Env → Observation Allocator (Except ProgramError Unit)) : Prop :=
 ∀ allocator, TX1_344.RowSpec_344 V P C (fun a sdk env => project (impl a ⟨sdk,allocator⟩ env))

/-- G2 in the full physical-adapter carrier, with arbitrary initial/final
allocator states explicit. It applies to every returned invocation without
Root0 or a selected-occurrence premise. The packet is not installed here. -/
theorem g2 {Allocator : Type} (L : PoolLib) (D : DeployedIds) (V : TX2_241.V2Lib)
 (w : Bytes → Bytes → Bytes → Spec (Except V.VErr Unit))
 (impl : TX2_240.Args → World Allocator → Env → Observation Allocator (Except ProgramError Unit))
 (packet : Packet240 L D (TCK.weaken V w) impl)
 (a : TX2_240.Args) (before after : World Allocator) (env : Env)
 (reply : Except ProgramError Unit) (events : List Event)
 (returned : impl a before env=⟨.returned reply after,events⟩) :
 PayloadFrame before.sdk after.sdk := by
 apply NMV_G2.weak_frame L D V w _ (packet before.allocator) a before.sdk after.sdk env reply events
 change project (impl a ⟨before.sdk,before.allocator⟩ env)=_
 cases before with | mk sdk allocator => rw [returned]; rfl

/-- Full-carrier version retaining every borrow-token cell field as well
as the exact token-counter advance; allocator pre/post values stay explicit. -/
theorem g2_sdk {Allocator : Type} (L : PoolLib) (D : DeployedIds) (V : TX2_241.V2Lib)
 (w : Bytes → Bytes → Bytes → Spec (Except V.VErr Unit))
 (impl : TX2_240.Args → World Allocator → Env → Observation Allocator (Except ProgramError Unit))
 (packet : Packet240 L D (TCK.weaken V w) impl)
 (a : TX2_240.Args) (before after : World Allocator) (env : Env)
 (reply : Except ProgramError Unit) (events : List Event)
 (returned : impl a before env=⟨.returned reply after,events⟩) :
 after.sdk.cells=before.sdk.cells ∧
 after.sdk.next=before.sdk.next+(if TX2_240.badRoute a then 0 else 7) := by
 apply NMV_G2State.weak_sdk L D V w _ (packet before.allocator) a before.sdk after.sdk env reply events
 change project (impl a ⟨before.sdk,before.allocator⟩ env)=_
 cases before with | mk sdk allocator => rw [returned]; rfl

#print axioms g2_sdk
#print axioms g2
end NMV_FullState
