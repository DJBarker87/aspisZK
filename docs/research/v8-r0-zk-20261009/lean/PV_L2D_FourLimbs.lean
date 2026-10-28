import PV_L2D_ScalarPort
import Mathlib.Tactic
set_option autoImplicit false
namespace PV_L2D_FourLimbs
open PV_L2D_ScalarPort
variable {S W : Type}

structure Collected (S W : Type) where
  value : Option (List Nat)
  after : S
  consumed : Nat
  events : List (Event W)
  counts : List (Nat × Bool)

def collect (next : S → Draw S W) (cap : Nat) : Nat → S → Collected S W
  | 0,s => ⟨some [],s,0,[],[]⟩
  | k+1,s =>
    let a:=sample next cap 0 s
    match a.value with
    | none => ⟨none,a.after,a.consumed,a.events,[(a.consumed,false)]⟩
    | some v =>
      let b:=collect next cap k a.after
      ⟨(v::·) <$> b.value,b.after,a.consumed+b.consumed,a.events++b.events,
        (a.consumed,true)::b.counts⟩

/-- Explicit source ordering of the four short-circuit scalar calls.
CM31::new only constructs a two-field record, so adds no branch/index/loop.
The actual decoder and constructor binding is a separate source obligation. -/
def sourceFour (next : S → Draw S W) (cap : Nat) (s : S) :
    Option (List Nat) × S × List (Event W) :=
  let a:=sample next cap 0 s
  match a.value with
  | none => (none,a.after,a.events)
  | some x =>
    let b:=sample next cap 0 a.after
    match b.value with
    | none => (none,b.after,a.events++b.events)
    | some y =>
      let c:=sample next cap 0 b.after
      match c.value with
      | none => (none,c.after,a.events++b.events++c.events)
      | some z =>
        let d:=sample next cap 0 c.after
        ((fun w=>[x,y,z,w]) <$> d.value,d.after,a.events++b.events++c.events++d.events)

theorem complete_four (next : S → Draw S W) (cap : Nat) (s : S) :
    sourceFour next cap s =
      ((collect next cap 4 s).value,(collect next cap 4 s).after,(collect next cap 4 s).events) := by
  unfold sourceFour
  cases ha : (sample next cap 0 s).value with
  | none => simp [collect,ha]
  | some x =>
    cases hb : (sample next cap 0 (sample next cap 0 s).after).value with
    | none => simp [collect,ha,hb]
    | some y =>
      cases hc : (sample next cap 0 (sample next cap 0 (sample next cap 0 s).after).after).value with
      | none => simp [collect,ha,hb,hc,List.append_assoc]
      | some z =>
        cases hd : (sample next cap 0 (sample next cap 0 (sample next cap 0 (sample next cap 0 s).after).after).after).value <;>
          simp [collect,ha,hb,hc,hd,List.append_assoc]
#print axioms complete_four

theorem consumed_bound (next : S → Draw S W) (cap k : Nat) (s : S) :
    (collect next cap k s).consumed≤cap*k := by
  induction k generalizing s with
  | zero => simp [collect]
  | succ k ih =>
    have h:=PV_L2D_ScalarPort.consumed_bound next cap 0 s
    have t:=ih (sample next cap 0 s).after
    cases hv : (sample next cap 0 s).value <;> simp [collect,hv,Nat.mul_succ] <;> omega
#print axioms consumed_bound

theorem counts_bound (next : S → Draw S W) (cap k : Nat) (s : S) :
    (collect next cap k s).counts.length≤k := by
  induction k generalizing s with
  | zero => simp [collect]
  | succ k ih =>
    have t:=ih (sample next cap 0 s).after
    cases hv : (sample next cap 0 s).value <;> simp [collect,hv,Nat.mul_succ] <;> omega
#print axioms counts_bound

theorem success_length (next : S → Draw S W) (cap k : Nat) (s : S) (vs : List Nat)
    (h : (collect next cap k s).value=some vs) : vs.length=k := by
  induction k generalizing s vs with
  | zero => simpa [collect] using h.symm
  | succ k ih =>
    cases hv : (sample next cap 0 s).value with
    | none => simp [collect,hv] at h
    | some v =>
      cases ht : (collect next cap k (sample next cap 0 s).after).value with
      | none => simp [collect,hv,ht] at h
      | some xs =>
        have hx:=ih _ xs ht
        simp [collect,hv,ht] at h
        subst vs
        simp [hx]
#print axioms success_length

theorem four_bound (next : S → Draw S W) (s : S) :
    (collect next 16 4 s).consumed≤64 := consumed_bound next 16 4 s
#print axioms four_bound
end PV_L2D_FourLimbs
