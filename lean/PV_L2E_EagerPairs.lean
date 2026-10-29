import PV_L2E_HostQuerySafety
set_option autoImplicit false
namespace PV_L2E_EagerPairs

structure Pairs (H : Type) where
  blocks : List H
  advances : List H
  finalState : H

inductive Event where
  | block (index : Nat)
  | advance (index : Nat)
  deriving DecidableEq

/-- Digest is an explicit deterministic argument. This does not claim the
native digest's control trace is independent of its bytes. -/
def generate {H : Type} (digest : H → Bool → H) : Nat → Nat → H → Pairs H × List Event
  | _,0,s => (⟨[],[],s⟩,[])
  | i,n+1,s =>
    let b := digest s false
    let a := digest s true
    let rest := generate digest (i+1) n a
    (⟨b::rest.1.blocks,a::rest.1.advances,rest.1.finalState⟩,
      [.block i,.advance i] ++ rest.2)

def plan : Nat → Nat → List Event
  | _,0 => []
  | i,n+1 => [.block i,.advance i] ++ plan (i+1) n

theorem lengths {H : Type} (digest : H → Bool → H) (i n : Nat) (s : H) :
    (generate digest i n s).1.blocks.length=n ∧
    (generate digest i n s).1.advances.length=n := by
  induction n generalizing i s with
  | zero => exact ⟨rfl,rfl⟩
  | succ n ih => simp only [generate,List.length_cons]; exact ⟨congrArg Nat.succ (ih _ _).1,congrArg Nat.succ (ih _ _).2⟩

theorem trace_fixed {H : Type} (digest : H → Bool → H) (i n : Nat) (s : H) :
    (generate digest i n s).2=plan i n := by
  induction n generalizing i s with
  | zero => rfl
  | succ n ih => simp only [generate,ih,plan]

theorem final_state {H : Type} (digest : H → Bool → H) (i n : Nat) (s : H) :
    (generate digest i n s).1.finalState=(fun a => digest a true)^[n] s := by
  induction n generalizing i s with
  | zero => rfl
  | succ n ih => simpa only [generate,Function.iterate_succ_apply] using ih (i+1) (digest s true)

/-- Every eager pair is generated regardless of what a later scanner does. -/
theorem scan_cannot_truncate {H Q : Type} (digest : H → Bool → H)
    (scan : List H → Q) (i n : Nat) (s : H) :
    ((generate digest i n s).2,scan (generate digest i n s).1.blocks).1=plan i n :=
  trace_fixed digest i n s

#print axioms lengths
#print axioms trace_fixed
#print axioms final_state
#print axioms scan_cannot_truncate
end PV_L2E_EagerPairs
