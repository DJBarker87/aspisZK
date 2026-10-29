import PV_L2E_ArrayCarry
set_option autoImplicit false
namespace PV_L2E_ArrayCarryTrace
open PV_L2E_ArrayMemory PV_L2D_DivisionBounds

inductive Event where
  | loopGuard (index : Nat) (live : Bool)
  | readGuard (index : Nat) (valid : Bool)
  | read (index : Nat)
  | writeGuard (index : Nat) (valid : Bool)
  | write (index : Nat)
  deriving DecidableEq

def execute (width : Nat) : Nat → Nat → Nat → Memory → (Memory × Nat) × List Event
  | i,0,c,a => ((a,c),[.loopGuard i false])
  | i,n+1,c,a =>
    let sum := a i+c
    let rest := execute width (i+1) n (sum/P) (store a i (sum%P))
    (rest.1,[.loopGuard i true,.readGuard i (decide (i<width)),.read i,
      .writeGuard i (decide (i<width)),.write i] ++ rest.2)

def plan (width : Nat) : Nat → Nat → List Event
  | i,0 => [.loopGuard i false]
  | i,n+1 => [.loopGuard i true,.readGuard i (decide (i<width)),.read i,
      .writeGuard i (decide (i<width)),.write i] ++ plan width (i+1) n

theorem complete (width i n c : Nat) (a : Memory) :
    execute width i n c a=(PV_L2E_ArrayCarry.run i n c a,plan width i n) := by
  induction n generalizing i c a with
  | zero => rfl
  | succ n ih => simp only [execute,ih,PV_L2E_ArrayCarry.run,plan]

def Safe : Event → Prop
  | .readGuard _ b | .writeGuard _ b => b=true
  | _ => True

theorem plan_safe (width i n : Nat) (cap : i+n≤width) :
    ∀ e∈plan width i n,Safe e := by
  induction n generalizing i with
  | zero => simp [plan,Safe]
  | succ n ih =>
    have hi : i<width := by omega
    have ht := ih (i+1) (by omega)
    simp only [plan,List.mem_append,List.mem_cons,List.not_mem_nil,or_false,or_assoc]
    intro e he
    rcases he with rfl|rfl|rfl|rfl|rfl|he <;> simp_all [Safe]

theorem arithmetic_safe (d a : Nat) (hd : d<P) (ha : a≤P) :
    d+a<2^64 ∧ (d+a)/P<B ∧ (d+a)%P<B := by
  have hq := PV_L2E_CarryTrace.one_step_carry d a hd ha
  have hm := Nat.mod_lt (d+a) (by decide : 0<P)
  norm_num only [P,B] at *
  omega

#print axioms complete
#print axioms plan_safe
#print axioms arithmetic_safe
end PV_L2E_ArrayCarryTrace
