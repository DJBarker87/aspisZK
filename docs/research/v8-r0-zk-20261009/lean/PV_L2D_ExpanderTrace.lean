import PV_L2D_ExpanderPort
import PV_L2D_ScalarRender
set_option autoImplicit false
namespace PV_L2D_ExpanderTrace
open PV_L2D_ExpanderPort PV_L2D_ScalarPort PV_L2D_ScalarRender
abbrev Clock := UInt64 × Fin 9

def clock (s : State) : Clock := (s.counter,s.word)
def zeroHash : Seed → UInt64 → Cache := fun _ _ _ => 0
def liftClock (c : Clock) : State := ⟨fun _ => 0,c.1,c.2,fun _ => 0⟩
def tick (c : Clock) : Clock := clock (next zeroHash (liftClock c)).after
def wordTrace (c : Clock) := (next zeroHash (liftClock c)).events

theorem next_clock (hash : Seed → UInt64 → Cache) (s : State) :
    clock (next hash s).after=tick (clock s) := by rfl
#print axioms next_clock

theorem next_trace (hash : Seed → UInt64 → Cache) (s : State) :
    (next hash s).events=wordTrace (clock s) :=
  trace_public hash zeroHash s (liftClock (clock s)) rfl rfl
#print axioms next_trace

theorem scalar_trace (hash : Seed → UInt64 → Cache) (n retry : Nat) (s : State) :
    (sample (next hash) n retry s).events = render tick wordTrace
      (sample (next hash) n retry s).consumed retry (clock s)
      (sample (next hash) n retry s).value.isSome :=
  trace_render (next hash) clock tick wordTrace (next_clock hash) (next_trace hash) n retry s
#print axioms scalar_trace

/-- This is the actual public initial cursor. No source seed or accepted
field value occurs in the trace reconstruction. -/
theorem initial_clock (seed : Seed) : clock (initial seed) = (0,⟨8,by decide⟩) := rfl
#print axioms initial_clock
end PV_L2D_ExpanderTrace
