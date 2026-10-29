import PV_L2E_CarryValue
set_option autoImplicit false
namespace PV_L2E_GammaTrace
open PV_L2D_DivisionBounds PV_L2E_CarryTrace PV_L2E_CarryValue

inductive Event where
  | carry (event : PV_L2E_CarryTrace.Event)
  | wrapped (taken : Bool)
  deriving DecidableEq

structure Output where
  digits : List Nat
  finalCarry : Nat
  events : List Event

def run (q : Nat) (ds : List Nat) : Output :=
  let first := PV_L2E_CarryTrace.run 0 (q+1) ds
  if first.1.2=0 then
    ⟨first.1.1,0,first.2.map Event.carry ++ [.wrapped false]⟩
  else
    let second := PV_L2E_CarryTrace.run 0 1 first.1.1
    ⟨second.1.1,second.1.2,
      first.2.map Event.carry ++ [.wrapped true] ++ second.2.map Event.carry⟩

def plan (width : Nat) (wrapped : Bool) : List Event :=
  (PV_L2E_CarryTrace.plan 0 width).map Event.carry ++
    if wrapped then [.wrapped true] ++ (PV_L2E_CarryTrace.plan 0 width).map Event.carry
    else [.wrapped false]

theorem trace_by_carry (q : Nat) (ds : List Nat) :
    (run q ds).events=plan ds.length (decide ((PV_L2E_CarryTrace.run 0 (q+1) ds).1.2≠0)) := by
  by_cases h : (PV_L2E_CarryTrace.run 0 (q+1) ds).1.2=0
  · simp [run,plan,h,PV_L2E_CarryTrace.trace_constant,PV_L2E_CarryTrace.length]
  · simp [run,plan,h,PV_L2E_CarryTrace.trace_constant,PV_L2E_CarryTrace.length,
      List.append_assoc]

theorem output_length (q : Nat) (ds : List Nat) : (run q ds).digits.length=ds.length := by
  dsimp only [run]
  split_ifs <;> simp only [PV_L2E_CarryTrace.length]

theorem output_bounds (q : Nat) (ds : List Nat) : ∀ d∈(run q ds).digits,d<P := by
  dsimp only [run]
  split_ifs <;> exact digit_bounds _ _ _

/-- First-pass wrap leaves a small value; adding 1 cannot wrap again.
The source's debug assertion is therefore a theorem, not an assumed success. -/
theorem second_carry_zero (q : Nat) (ds : List Nat) (hq : q≤256)
    (width : ds.length=8) (hd : ∀ d∈ds,d<P)
    (wrapped : (PV_L2E_CarryTrace.run 0 (q+1) ds).1.2≠0) :
    (PV_L2E_CarryTrace.run 0 1 (PV_L2E_CarryTrace.run 0 (q+1) ds).1.1).1.2=0 := by
  have hsmall : q+1≤P := by dsimp [P]; omega
  have hn : ds≠[] := by intro he; simp [he] at width
  have hc := final_carry 0 (q+1) ds hsmall hd hn
  have he : (PV_L2E_CarryTrace.run 0 (q+1) ds).1.2=1 := by omega
  have hv := wrapped_value_lt 0 (q+1) ds hd he
  apply no_wrap_of_small_sum
  rw [PV_L2E_CarryTrace.length,width]
  have hp : 257<P^8 := by norm_num [P]
  omega

#print axioms trace_by_carry
#print axioms output_length
#print axioms output_bounds
#print axioms second_carry_zero
end PV_L2E_GammaTrace
