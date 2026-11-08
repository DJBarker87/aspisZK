import PV_LIB_Graph
import PV_STX2_Native
set_option autoImplicit false
namespace PV_LIB_SPEC_Environment
open PV_STX_Machine PV_STX2_Syntax

/-- Source identity is distinct from activation numbering. A schedule is
indexed by emitted function/site and its actual dynamic occurrence. -/
structure Site where
  function : Nat
  statement : Nat
  deriving DecidableEq

structure Request (W : Type) where
  site : Site
  occurrence : Nat
  arguments : List Data
  before : W

/-- Full reply channels, including source-encoded returned Err payloads,
post-world, ordered event suffix, faults, abort, divergence and pending.
Reservation and infallible allocation have distinct channels. No field is a
proof of a desired result or of witness independence. -/
structure Env (W E : Type) where
  allocation : Request W → Reply W E Data
  reservation : Request W → Reply W E Data
  leaf : PV_STX2_Native.Request Data → W → Reply W E Data

inductive Channel where
  | allocation | reservation
  deriving DecidableEq

def reply {W E : Type} (env : Env W E) (channel : Channel) (request : Request W) : Reply W E Data :=
  match channel with
  | .allocation => env.allocation request
  | .reservation => env.reservation request

/-- The graph includes world/events and every answer, not just returned values.
Binding an actual machine poll to its source request is a separate obligation. -/
def Law {W E : Type} (env : Env W E) (channel : Channel) (request : Request W)
    (out : Reply W E Data) : Prop := out = reply env channel request

def observe {W E : Type} (prior : List E) (r : Reply W E Data) :
    PV_LIB.Observation (Answer Data) W E :=
  match r.answer with
  | .fault .abort => .abort (prior ++ r.events)
  | _ => .returned r.answer r.world (prior ++ r.events)

/-- A source allocation can abort only when its actual indexed channel says so.
The caller must first establish that this request is reached in source order. -/
def ObservedLaw {W E : Type} (env : Env W E) (channel : Channel) (request : Request W)
    (prior : List E) (out : PV_LIB.Observation (Answer Data) W E) : Prop :=
  out = observe prior (reply env channel request)

theorem functional {W E : Type} (env : Env W E) (channel : Channel) (request : Request W)
    (a b : Reply W E Data) (ha : Law env channel request a) (hb : Law env channel request b) : a = b :=
  ha.trans hb.symm

theorem observed_functional {W E : Type} (env : Env W E) (channel : Channel) (request : Request W)
    (prior : List E) (a b : PV_LIB.Observation (Answer Data) W E)
    (ha : ObservedLaw env channel request prior a) (hb : ObservedLaw env channel request prior b) : a = b :=
  ha.trans hb.symm

theorem abort_prefix {W E : Type} (prior suffix : List E) (w : W) :
    observe prior (⟨.fault .abort,w,suffix⟩ : Reply W E Data) =
      PV_LIB.Observation.abort (prior ++ suffix) := rfl

/-- All-pending channels witness nonemptiness of Env itself. This does NOT
witness any conjunction of a row's machine/entry/source-adequacy obligations. -/
def pendingEnv (W E : Type) : Env W E :=
  ⟨fun r => ⟨.pending,r.before,[]⟩,
    fun r => ⟨.pending,r.before,[]⟩,
    fun _ w => ⟨.pending,w,[]⟩⟩

theorem nonempty (W E : Type) : Nonempty (Env W E) := ⟨pendingEnv W E⟩

#print axioms functional
#print axioms observed_functional
#print axioms abort_prefix
#print axioms nonempty
end PV_LIB_SPEC_Environment
