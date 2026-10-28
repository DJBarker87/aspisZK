import PV_L2D_FourLimbs
import PV_L2D_ExpanderTrace
set_option autoImplicit false
namespace PV_L2D_CollectedTrace
open PV_L2D_ScalarPort PV_L2D_FourLimbs PV_L2D_ExpanderPort PV_L2D_ExpanderTrace

def advance : Nat → Clock → Clock
  | 0,c => c
  | n+1,c => advance n (tick c)

theorem after_clock (hash : Seed → UInt64 → Cache) (n : Nat) (s : State) :
    clock (after (next hash) n s)=advance n (clock s) := by
  induction n generalizing s with
  | zero => rfl
  | succ n ih => simpa only [after,advance,next_clock] using ih (next hash s).after
#print axioms after_clock

theorem sample_after_clock (hash : Seed → UInt64 → Cache) (n retry : Nat) (s : State) :
    clock (sample (next hash) n retry s).after=
      advance (sample (next hash) n retry s).consumed (clock s) := by
  rw [after_exact,after_clock]
#print axioms sample_after_clock

def render : List (Nat × Bool) → Clock → List (Event WordEvent)
  | [],_ => []
  | (count,success)::xs,c =>
    PV_L2D_ScalarRender.render tick wordTrace count 0 c success ++
      render xs (advance count c)

theorem complete_trace (hash : Seed → UInt64 → Cache) (cap k : Nat) (s : State) :
    (collect (next hash) cap k s).events=
      render (collect (next hash) cap k s).counts (clock s) := by
  induction k generalizing s with
  | zero => rfl
  | succ k ih =>
    cases hv : (sample (next hash) cap 0 s).value with
    | none =>
      simp only [collect,hv,render,List.append_nil]
      simpa only [hv,Option.isSome_none] using scalar_trace hash cap 0 s
    | some v =>
      simp only [collect,hv,render]
      rw [scalar_trace,ih,sample_after_clock]
      simp only [hv,Option.isSome_some]
#print axioms complete_trace

/-- Reconstruction uses only the initial public clock, ordered per-limb
counts, and the terminal tags. It keeps failed prefixes and limb boundaries. -/
theorem same_counts (left right : Seed → UInt64 → Cache) (cap k : Nat) (s t : State)
    (hc : clock s=clock t)
    (hk : (collect (next left) cap k s).counts=(collect (next right) cap k t).counts) :
    (collect (next left) cap k s).events=(collect (next right) cap k t).events := by
  rw [complete_trace,complete_trace,hc,hk]
#print axioms same_counts
end PV_L2D_CollectedTrace
