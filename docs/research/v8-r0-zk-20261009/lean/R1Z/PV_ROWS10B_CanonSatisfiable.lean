import R1Z.PV_ROWS10B_CanonConsumed
set_option autoImplicit false
namespace R1Z.PV_ROWS10B_CanonSatisfiable
open Aeneas Aeneas.Std PV_ROWS10B_CanonConsumed
/-- Explicit model of the same four-limb interface, using the actual Aeneas
fixed arrays and their update/read operations. This is not the deployed run. -/
def limb (q : U32) (_ : Fin 4) : U32 := q

def zero28 : Array U32 28#usize := ⟨List.replicate 28 (0#u32), by simp⟩
def zero10 : Array U32 10#usize := ⟨List.replicate 10 (0#u32), by simp⟩
def event : Event U32 Unit Unit :=
  ⟨zero28, zero28, zero10, zero10, 0#usize, (), (), 0#u32, 0#u32⟩
def occurs (e : Event U32 Unit Unit) : Prop := e = event
def reached (p : Array U32 28#usize) (q : U32) : Prop := p = zero28 ∧ q = 0#u32

def interpolate (_ : Array U32 28#usize) : Result (Array U32 28#usize) := .ok zero28
def semantic (_ : Unit) : Result ((core.result.Result U32 Unit) × Unit) := .ok (.Ok (0#u32), ())

theorem zero_canonical : Canonical limb (0#u32) := by
  intro i; change 0 < 2147483647; omega

theorem all_links :
    PV_ROWS10B_Link_CallerPrefix reached occurs ∧
    PV_ROWS10B_Link_PrefixEquations occurs interpolate semantic ∧
    PV_ROWS10B_Link_RoundRange occurs ∧
    PV_ROWS10B_Link_Interpolation limb interpolate ∧
    PV_ROWS10B_Link_Semantic limb semantic ∧
    reached zero28 (0#u32) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ⟨rfl,rfl⟩⟩
  · intro p q hit
    rcases hit with ⟨hp,hq⟩
    exact ⟨event, rfl, hp.symm, hq.symm⟩
  · intro e he
    cases he
    exact ⟨rfl, rfl, rfl, rfl⟩
  · intro e he
    cases he
    change 0 < 10; omega
  · intro values p hp
    change Result.ok zero28 = Result.ok p at hp
    cases Result.ok.inj hp
    intro x hx
    change x ∈ List.replicate 28 (0#u32) at hx
    have same := (List.mem_replicate.mp hx).2
    rw [same]; exact zero_canonical
  · intro trace q after hs
    change Result.ok (core.result.Result.Ok (0#u32), ()) =
      Result.ok (core.result.Result.Ok q, after) at hs
    cases Result.ok.inj hs
    exact zero_canonical

/-- Conjunction satisfiability includes a reached event, preventing an empty
reachability relation from providing the only witness. -/
theorem satisfiable :
    ∃ (limb' : U32 → Fin 4 → U32)
      (reached' : Array U32 28#usize → U32 → Prop)
      (occurs' : Event U32 Unit Unit → Prop)
      (interpolate' : Array U32 28#usize → Result (Array U32 28#usize))
      (semantic' : Unit → Result ((core.result.Result U32 Unit) × Unit)),
      PV_ROWS10B_Link_CallerPrefix reached' occurs' ∧
      PV_ROWS10B_Link_PrefixEquations occurs' interpolate' semantic' ∧
      PV_ROWS10B_Link_RoundRange occurs' ∧
      PV_ROWS10B_Link_Interpolation limb' interpolate' ∧
      PV_ROWS10B_Link_Semantic limb' semantic' ∧
      reached' zero28 (0#u32) :=
  ⟨limb,reached,occurs,interpolate,semantic,all_links⟩
#print axioms zero_canonical
#print axioms all_links
#print axioms satisfiable
end R1Z.PV_ROWS10B_CanonSatisfiable
