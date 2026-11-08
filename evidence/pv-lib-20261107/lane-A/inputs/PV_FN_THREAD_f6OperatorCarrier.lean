import PV_FN_THREAD_f6CounterTest
set_option autoImplicit false
namespace PV_FN_THREAD_f6OperatorCarrier
open PV_STX2_Syntax PV_STX2_Store

abbrev Binary := String → Data → Data → Option Data

def ne (old : Binary) : Binary := fun op x y => match op,x,y with
  | "Ne",.number n,.number 0 => some (.boolean (decide (n ≠ 0)))
  | _,_,_ => old op x y

def lt (old : Binary) : Binary := fun op x y => match op,x,y with
  | "Lt",.number n,.number m => some (.boolean (decide (n < m)))
  | _,_,_ => old op x y

def gt (old : Binary) : Binary := fun op x y => match op,x,y with
  | "Gt",.number n,.number m => some (.boolean (decide (m < n)))
  | _,_,_ => old op x y

/-- Install source2200 in the base so existing generic own-source proofs reuse it. -/
def base {W : Type} (c : Carrier W Data) : Carrier W Data :=
  {c with binary := ne c.binary}

theorem ne_lt (old : Binary) : ne (lt old) = lt (ne old) := by
  funext op x y
  by_cases hn : op = "Ne"
  · subst op
    cases x <;> cases y <;> rfl
  · by_cases hl : op = "Lt"
    · subst op
      cases x <;> cases y <;> rfl
    · cases x <;> cases y <;> simp [ne,lt,hn,hl]

theorem ne_gt (old : Binary) : ne (gt old) = gt (ne old) := by
  funext op x y
  by_cases hn : op = "Ne"
  · subst op
    cases x <;> cases y <;> rfl
  · by_cases hg : op = "Gt"
    · subst op
      cases x <;> cases y <;> rfl
    · cases x <;> cases y <;> simp [ne,gt,hn,hg]

/-- Reconcile named operators symbolically, before inspecting any generated
store. The Lt/Gt/Ne shapes are disjoint and all other fields are unchanged. -/
theorem agreement {W : Type} (c : Carrier W Data) (b : Bool) :
    PV_FN_THREAD_f6CounterTest.carrier c b =
      PV_THR2_EntryDynamic.carrier (PV_THR2_ScopeLiterals.carrier (base c)) b := by
  let d := PV_THR2_EntryDynamic.carrier (PV_THR2_ScopeLiterals.carrier c) b
  change {d with binary := ne (lt (gt c.binary))} =
    {d with binary := lt (gt (ne c.binary))}
  rw [ne_lt,ne_gt]

#print axioms ne_lt
#print axioms ne_gt
#print axioms agreement
end PV_FN_THREAD_f6OperatorCarrier
