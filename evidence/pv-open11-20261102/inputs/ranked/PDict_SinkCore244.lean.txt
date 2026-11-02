import Std
set_option autoImplicit false
namespace R1Z.PDict_SinkCore244

structure Formatter (B O S : Type) where
  options : O
  sink : S
  emit : S → List B → Bool × S
  calls : List (List B)

/-- Bool denotes failure. Both success and failure retain the actual sink's
returned state and record its complete requested bytes. No atomicity premise. -/
def write {B O S : Type} (bytes : List B) (f : Formatter B O S) :
    Bool × Formatter B O S :=
  let (failed,sink) := f.emit f.sink bytes
  (failed,{ f with sink := sink, calls := f.calls ++ [bytes] })

theorem options_frame {B O S : Type} (bytes : List B) (f : Formatter B O S) :
    (write bytes f).2.options = f.options := rfl

theorem sink_exact {B O S : Type} (bytes : List B) (f : Formatter B O S) :
    ((write bytes f).1,(write bytes f).2.sink) = f.emit f.sink bytes := by
  simp only [write]

theorem calls_exact {B O S : Type} (bytes : List B) (f : Formatter B O S) :
    (write bytes f).2.calls = f.calls ++ [bytes] := rfl

theorem emit_frame {B O S : Type} (bytes : List B) (f : Formatter B O S) :
    (write bytes f).2.emit = f.emit := rfl

/-- Explicit caller schedule, including calls made after earlier failures. A
caller that stops on failure supplies its actual prefix, never a rewritten log. -/
def writes {B O S : Type} : List (List B) → Formatter B O S → List Bool × Formatter B O S
  | [], f => ([],f)
  | bytes::rest, f =>
    let (failed,next) := write bytes f
    let (failures,final) := writes rest next
    (failed::failures,final)

theorem writes_inventory {B O S : Type} (schedule : List (List B))
    (f : Formatter B O S) :
    (writes schedule f).2.options = f.options ∧
    (writes schedule f).2.emit = f.emit ∧
    (writes schedule f).2.calls = f.calls ++ schedule ∧
    (writes schedule f).1.length = schedule.length := by
  induction schedule generalizing f with
  | nil => exact ⟨rfl,rfl,by simp only [writes,List.append_nil],rfl⟩
  | cons bytes rest ih =>
    obtain ⟨options,emit,calls,length⟩ := ih (write bytes f).2
    exact ⟨options,emit,by simpa only [writes,calls,calls_exact,List.append_assoc,List.singleton_append],
      by simpa only [writes,List.length_cons] using congrArg Nat.succ length⟩

/-- A relation between concrete and quotient sink states suffices for one
transition. This hypothesis concerns only the sink leaf, never whole-caller
equivalence or its distribution. Native Formatter delegation is separate. -/
theorem transport {B O S T : Type} (rel : S → T → Prop)
    (native : S → List B → Bool × S) (reference : T → List B → Bool × T)
    (leaf : ∀ s t bytes, rel s t →
      (native s bytes).1 = (reference t bytes).1 ∧
        rel (native s bytes).2 (reference t bytes).2)
    (s : S) (t : T) (options : O) (calls : List (List B)) (bytes : List B)
    (related : rel s t) :
    (write bytes (⟨options,s,native,calls⟩ : Formatter B O S)).1 =
      (write bytes (⟨options,t,reference,calls⟩ : Formatter B O T)).1 ∧
    rel (write bytes (⟨options,s,native,calls⟩ : Formatter B O S)).2.sink
      (write bytes (⟨options,t,reference,calls⟩ : Formatter B O T)).2.sink :=
  leaf s t bytes related

#print axioms options_frame
#print axioms sink_exact
#print axioms calls_exact
#print axioms emit_frame
#print axioms writes_inventory
#print axioms transport
end R1Z.PDict_SinkCore244
