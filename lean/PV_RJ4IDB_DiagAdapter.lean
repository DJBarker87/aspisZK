import PV_RJ4IDB_Decoder
set_option autoImplicit false
namespace PV_RJ4IDB
variable {S A : Type}
def diagTerminal : PV_DIAG3.Exit A → Terminal A
 | .value a => .success a
 | .panic p => .panic p
 | .abort p => .abort p
 | .diverge => .diverge

def diagTrace (x : PV_DIAG3.Execution S A) : Trace A :=
 ⟨x.events.map Event.diagnostic3,diagTerminal x.exit⟩

theorem diag_events (x : PV_DIAG3.Execution S A) :
 (decoder (diagTrace x)).errorsStderr3 = x.events := by
 change diagnostics3 (x.events.map Event.diagnostic3) = x.events
 have aux : ∀ es : List PV_DIAG3.Event, diagnostics3 (es.map Event.diagnostic3) = es := by
  intro es
  induction es with
  | nil => rfl
  | cons e es ih => change e :: diagnostics3 (es.map Event.diagnostic3) = e :: es; rw [ih]
 exact aux x.events

theorem diag_prefix (before : List PV_DIAG3.Event) (x : PV_DIAG3.Execution S A) :
 (diagTrace (PV_DIAG3.prepend before x)).events =
 before.map Event.diagnostic3 ++ (diagTrace x).events := by
 simp [diagTrace,PV_DIAG3.prepend,List.map_append]

theorem diag_bind_abort (es : List PV_DIAG3.Event) (s : S) (c : PV_DIAG3.Crash)
 (f : A → PV_DIAG3.Op S Unit) :
 diagTrace (PV_DIAG3.bind ⟨es,s,.abort c⟩ f) = ⟨es.map Event.diagnostic3,.abort c⟩ := rfl

theorem diag_bind_diverge (es : List PV_DIAG3.Event) (s : S)
 (f : A → PV_DIAG3.Op S Unit) :
 diagTrace (PV_DIAG3.bind ⟨es,s,.diverge⟩ f) = ⟨es.map Event.diagnostic3,.diverge⟩ := rfl
#print axioms diag_events
#print axioms diag_prefix
#print axioms diag_bind_abort
#print axioms diag_bind_diverge
end PV_RJ4IDB
