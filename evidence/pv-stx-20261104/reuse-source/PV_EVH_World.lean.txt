import PV_RJ4IDB_NativeTrace
import R1Z.ProverRwFullFuns
/-! D520 prover world substrate. This module is not the prover entry producer.
Primitive events are emitted before control returns, rather than decoded from
its final Result. No native adequacy or entropy distribution is assumed. -/
set_option autoImplicit false
namespace PV_EVH_World
open Aeneas Aeneas.Std ProverRwFull
open PV_RJ4IDB (Bytes NativeEvent)

structure FileState where
  path : Bytes
  delivered : Bytes
  durable : Bytes

structure World where
  entropyCursor : Nat := 0
  files : List FileState := []
  oracleHistory : List (Bytes × Bytes) := []
  attempts : Nat := 0
  retries : Nat := 0
  allocations : Nat := 0
  clockReads : Nat := 0

structure Run (A : Type) where
  result : Result A
  world : World
  events : List NativeEvent

abbrev M (A : Type) := World → Run A

def lift {A : Type} (r : Result A) : M A := fun w => ⟨r,w,[]⟩
def bind {A B : Type} (m : M A) (k : A → M B) : M B := fun w =>
  let r := m w
  match r.result with
  | .ok a => let s := k a r.world; ⟨s.result,s.world,r.events ++ s.events⟩
  | .fail e => ⟨.fail e,r.world,r.events⟩
  | .div => ⟨.div,r.world,r.events⟩

instance : Monad M where
  pure a := lift (.ok a)
  bind := bind

def emit (es : List NativeEvent) (step : World → World) : M Unit :=
  fun w => ⟨.ok (),step w,es⟩

theorem bind_fail {A B : Type} (m : M A) (k : A → M B)
    (w : World) (e : Error) (h : (m w).result = .fail e) :
    bind m k w = ⟨.fail e,(m w).world,(m w).events⟩ := by
  simp only [bind,h]

theorem bind_div {A B : Type} (m : M A) (k : A → M B)
    (w : World) (h : (m w).result = .div) :
    bind m k w = ⟨.div,(m w).world,(m w).events⟩ := by
  simp only [bind,h]

theorem bind_assoc {A B C : Type} (m : M A) (k : A → M B) (f : B → M C) :
    bind (bind m k) f = bind m (fun a => bind (k a) f) := by
  funext w
  cases hm : (m w).result with
  | fail e => simp only [bind,hm]
  | div => simp only [bind,hm]
  | ok a => cases hk : (k a (m w).world).result <;>
      simp only [bind,hm,hk,List.append_assoc]

/-- Fixed-dictionary compatibility is a statement about every reached answer;
it is not a new trust item and is false for advancing reject/success entropy. -/
def FixedView {A : Type} (m : M A) (r : Result A) : Prop :=
  ∀ w, (m w).result = r

theorem fixed_lift {A : Type} (r : Result A) : FixedView (lift r) r := fun _ => rfl

theorem fixed_bind {A B : Type} (m : M A) (k : A → M B)
    (r : Result A) (f : A → Result B) (hm : FixedView m r)
    (hk : ∀ a, FixedView (k a) (f a)) :
    FixedView (bind m k) (Aeneas.Std.bind r f) := by
  intro w
  cases hr : r with
  | ok a => simp only [bind,hm w,hr]; exact hk a _
  | fail e => simp only [bind,hm w,hr,Aeneas.Std.bind]
  | div => simp only [bind,hm w,hr,Aeneas.Std.bind]

def attempt : M Unit := fun w =>
  ⟨.ok (),{w with attempts := w.attempts + 1},[.count (w.attempts + 1)]⟩

def retry : M Unit := fun w =>
  ⟨.ok (),{w with retries := w.retries + 1},[.rejection w.attempts]⟩

/-- Query order and duplicate addresses are retained. The answer function is
still an explicit boundary; it does not receive a fabricated whole trace. -/
def query (answer : World → Bytes → Result Bytes) (address : Bytes) : M Bytes := fun w =>
  match answer w address with
  | .ok b => ⟨.ok b,{w with oracleHistory := w.oracleHistory ++ [(address,b)]},[.side [] address,.oracle address b]⟩
  | .fail e => ⟨.fail e,w,[.side [] address]⟩
  | .div => ⟨.div,w,[.side [] address]⟩

/-- Neither this model world nor its primitive success is an entry witness. -/
theorem query_model (w : World) (address answer : Bytes) :
    (query (fun _ _ => .ok answer) address w).result = .ok answer ∧
    (query (fun _ _ => .ok answer) address w).world.oracleHistory =
      w.oracleHistory ++ [(address,answer)] ∧
    (query (fun _ _ => .ok answer) address w).events = [.side [] address,.oracle address answer] :=
  ⟨rfl,rfl,rfl⟩

/-- D520 client fields remain inputs, not claimed outputs of this substrate. -/
structure D520ClientOpen where
  D520_client_before_OPEN : List NativeEvent
  D520_client_after_OPEN : List NativeEvent

/-- Result is retained directly until an actual terminal conversion is installed. -/
def oraclePrefix {A : Type} (r : Run A) := PV_RJ4IDB.nativeOracle r.events
def countTrace {A : Type} (r : Run A) :=
  (PV_RJ4IDB.nativeCounts r.events,PV_RJ4IDB.nativeRejections r.events)
def nonceFileTrace {A : Type} (r : Run A) := PV_RJ4IDB.nativeFiles r.events

theorem oracle_projection {A : Type} (r : Run A) :
    oraclePrefix r = PV_RJ4IDB.nativeOracle r.events := rfl

theorem count_projection {A : Type} (r : Run A) :
    countTrace r = (PV_RJ4IDB.nativeCounts r.events,
      PV_RJ4IDB.nativeRejections r.events) := rfl

theorem nonce_projection {A : Type} (r : Run A) :
    nonceFileTrace r = PV_RJ4IDB.nativeFiles r.events := rfl

#print axioms bind_fail
#print axioms bind_div
#print axioms bind_assoc
#print axioms fixed_lift
#print axioms fixed_bind
#print axioms query_model
#print axioms oracle_projection
#print axioms count_projection
#print axioms nonce_projection
end PV_EVH_World
