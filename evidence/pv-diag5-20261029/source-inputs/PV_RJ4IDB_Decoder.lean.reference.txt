import PV_RJ4IDB_Channels
set_option autoImplicit false
namespace PV_RJ4IDB
structure Observation (A : Type) where
 /-- Retains cross-channel order even when projections alone would not. -/
 ordered : List Event
 terminal : Terminal A
 fileWrites : List FileOp
 returnedJSON : List Bytes
 stdoutJSON : List (Bytes × Bytes)
 errorsStderr2 : List PV_DIAG2.Effect
 errorsStderr3 : List PV_DIAG3.Event
 attemptCounts : List Nat
 prove_wall_seconds : List Bytes
 queryPrefix : List (Bytes × Bytes)
 rejectionPrefix : List Nat
 retainedSideChannels : List (Bytes × Bytes)
 deriving Repr

def decoder {A : Type} (t : Trace A) : Observation A :=
 ⟨t.events,t.terminal,files t.events,json t.events,stdout t.events,
 diagnostics2 t.events,diagnostics3 t.events,counts t.events,times t.events,
 oracle t.events,rejections t.events,sideChannels t.events⟩

theorem decoder_injective {A : Type} (l r : Trace A) :
 decoder l = decoder r → l = r := by
 intro h
 have he := congrArg Observation.ordered h
 have ht := congrArg Observation.terminal h
 cases l; cases r; cases he; cases ht; rfl

theorem failure_prefix (es : List Event) (e : Bytes) :
 (decoder (⟨es,.failure e⟩ : Trace Unit)).ordered = es := rfl

theorem divergence_prefix (es : List Event) :
 (decoder (⟨es,.diverge⟩ : Trace Unit)).ordered = es := rfl

theorem panic_prefix (es : List Event) (p : PV_DIAG3.Panic) :
 (decoder (⟨es,.panic p⟩ : Trace Unit)).ordered = es := rfl

theorem abort_prefix (es : List Event) (p : PV_DIAG3.Crash) :
 (decoder (⟨es,.abort p⟩ : Trace Unit)).ordered = es := rfl
#print axioms decoder_injective
#print axioms failure_prefix
#print axioms divergence_prefix
#print axioms panic_prefix
#print axioms abort_prefix
end PV_RJ4IDB
