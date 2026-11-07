import NLU_State
set_option autoImplicit false
noncomputable section
namespace AspisR1.NMC_Parent
open Aeneas Aeneas.Std Result AspisR1PublicPreparation
abbrev Claims := NLC_Finish.Claims
/-- An allocation identity and its complete value travel together. An address
alone never supplies its pointee; installation uses the returned child value. -/
structure OwnedClaims where
 identity : Nat
 value : Claims
/-- Arbitrary non-Claims storage is retained with its exact extent, alignment,
base and per-byte initializedness. Claims is the fully initialized typed
region obtained from the CLOSED unsafe child packet and pinned std model. -/
inductive Region where
 | raw (base extent alignment : Nat) (bytes : Nat → Option U8)
 | claims (value : Claims)
abbrev Heap := Nat → Option Region
/-- All original arguments and initialized local slots are in source.machine;
allocator and rest heap are carried explicitly rather than as a live Bool.
This is a segment interface, not yet an interpretation of compiled finish. -/
structure State (A H : Type) where
 source : NLU.State H
 allocator : A
 heap : Heap
 claims : Option OwnedClaims
/-- The SINGLE returned allocation is installed at its actual identity.
Every disjoint cell retains its own old value. No fresh unrelated heap chosen. -/
def write (heap : Heap) (owner : Nat) (value : Option Claims) : Heap :=
 fun address=>if address=owner then value.map Region.claims else heap address
/-- A Rust Box borrow is an immutable view of the same complete payload. -/
def Bound {A H : Type} (s : State A H) : Prop :=
 match s.claims with
 | none => s.source.machine.locals.claims=none
 | some live => s.heap live.identity=some (.claims live.value) ∧
   s.source.machine.locals.claims=some live.value
/-- On abort there is no invented after-heap. The last entered frame is
retained, and the entered child's internal effect prefix is separate. -/
inductive Exit (A H R : Type) where
 | returned (value : R) (after : State A H)
 | aborted (error : Error) (lastEntered : State A H)
 | diverged (lastEntered : State A H)
end AspisR1.NMC_Parent
end
