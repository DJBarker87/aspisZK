import NMV_WeakFold
set_option autoImplicit false
namespace NMV_PhysicalCarrier
open RSL

/-- Adapter-facing carrier: neither the COMPLETE SDK/runtime world nor its
COMPLETE allocator is replaced by a counter or by the RSL view. The A3/A4
owner chooses the concrete types and proves the representation map. -/
structure World (FullSdk Allocator : Type) where
 sdk : FullSdk
 allocator : Allocator

inductive End (FullSdk Allocator A : Type) where
 | returned (reply : A) (post : World FullSdk Allocator)
 | aborted
 | diverged

structure Observation (FullSdk Allocator A : Type) where
 ending : End FullSdk Allocator A
 events : List Event

def project {FullSdk Allocator A : Type} (view : FullSdk → SdkState)
 (o : Observation FullSdk Allocator A) : Obs (A × SdkState) :=
 ⟨match o.ending with
 | .returned reply post => .ret (reply,view post.sdk)
 | .aborted => .abort
 | .diverged => .diverge,o.events⟩

def Packet240 {FullSdk Allocator : Type} (view : FullSdk → SdkState)
 (L : PoolLib) (D : DeployedIds) (V : TX2_241.V2Lib)
 (impl : TX2_240.Args → World FullSdk Allocator → Env →
   Observation FullSdk Allocator (Except ProgramError Unit)) : Prop :=
 ∀ a before env, TX2_240.Domain V a (view before.sdk) →
 TX2_240.Ref L D V a (view before.sdk) env (project view (impl a before env))

def Packet344 {FullSdk Allocator : Type} (view : FullSdk → SdkState)
 (V : VLib) (P : PreparedNew V) (C : TX1_345.S1Lib V)
 (impl : TX1_344.Args → World FullSdk Allocator → Env →
   Observation FullSdk Allocator (Except ProgramError Unit)) : Prop :=
 ∀ a before env, TX1_344.Domain a (view before.sdk) →
 TX1_344.Ref V P C a (view before.sdk) env (project view (impl a before env))

/-- G2 while retaining FULL SDK/allocator pre/post objects. The conclusion
is exactly the RSL cell/token frame; extra physical-field frame/representation
is A3/A4/A5 work. No equality of unmodelled fields is invented. -/
theorem g2 {FullSdk Allocator : Type} (view : FullSdk → SdkState)
 (L : PoolLib) (D : DeployedIds) (V : TX2_241.V2Lib)
 (w : Bytes → Bytes → Bytes → Spec (Except V.VErr Unit))
 (impl : TX2_240.Args → World FullSdk Allocator → Env →
   Observation FullSdk Allocator (Except ProgramError Unit))
 (packet : Packet240 view L D (TCK.weaken V w) impl)
 (a : TX2_240.Args) (before after : World FullSdk Allocator) (env : Env)
 (reply : Except ProgramError Unit) (events : List Event)
 (returned : impl a before env=⟨.returned reply after,events⟩) :
 (view after.sdk).cells=(view before.sdk).cells ∧
 (view after.sdk).next=(view before.sdk).next+(if TX2_240.badRoute a then 0 else 7) := by
 have h := packet a before env (TCK.domain240_weaken V w a (view before.sdk))
 rw [returned] at h
 exact NMV_G2State.reference_sdk L D (TCK.weaken V w) a (view before.sdk)
   (view after.sdk) env reply events h

#print axioms g2
end NMV_PhysicalCarrier
