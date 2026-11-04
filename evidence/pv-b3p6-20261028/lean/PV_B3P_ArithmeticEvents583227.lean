import PV_B3P_DominatedEvents578227
namespace PV_B3P_ArithmeticEvents583227
open Aeneas Aeneas.Std PV_B3P_PanicPatterns571227 PV_B3P_InitializerEvents578227
set_option autoImplicit false
/-- An arithmetic observation keeps the actual scalar operand. A bounded input
uses the source comparison as a test, rather than taking its truth as input. -/
inductive Expr where
  | literal (value : Nat)
  | bounded (value limit : Nat)
  | remainder (value divisor : Nat)
  | bitAnd (value mask : Nat)
  | quotient (input : Expr) (divisor : Nat)
  | add (left right : Expr) (modulus : Nat)
  | mul (left right : Expr) (modulus : Nat)

def limit : Expr → Nat
  | .literal value => value+1
  | .bounded _ bound => bound
  | .remainder _ divisor => divisor
  | .bitAnd _ mask => mask+1
  | .quotient input divisor => (limit input+divisor-1)/divisor
  | .add left right _ => limit left + limit right - 1
  | .mul left right _ => (limit left-1)*(limit right-1)+1

def evaluate : Expr → Option Nat
  | .literal value => some value
  | .bounded value bound => if value < bound then some value else none
  | .remainder value divisor => if 0 < divisor then some (value%divisor) else none
  | .bitAnd value mask => some (value &&& mask)
  | .quotient input divisor => if 0 < divisor then (evaluate input).map (·/divisor) else none
  | .add left right modulus => do
      let a ← evaluate left
      let b ← evaluate right
      some ((a+b)%modulus)
  | .mul left right modulus => do
      let a ← evaluate left
      let b ← evaluate right
      some ((a*b)%modulus)

theorem evaluate_bound (expr : Expr) (value : Nat) (observed : evaluate expr = some value) :
    value < limit expr := by
  induction expr generalizing value with
  | literal n =>
    simp only [evaluate,Option.some.injEq] at observed
    subst value
    exact Nat.lt_succ_self n
  | bounded n bound =>
    simp only [evaluate] at observed
    split at observed
    · cases observed; assumption
    · cases observed
  | remainder n divisor =>
    simp only [evaluate] at observed
    split at observed
    · rename_i positive
      cases observed
      exact Nat.mod_lt n positive
    · cases observed
  | bitAnd n mask =>
    simp only [evaluate,Option.some.injEq] at observed
    subst value
    exact Nat.lt_succ_of_le (Nat.and_le_right (n:=n) (m:=mask))
  | quotient input divisor ih =>
    simp only [evaluate] at observed
    split at observed
    · rename_i positive
      cases h : evaluate input with
      | none => simp only [h,Option.map_none] at observed; cases observed
      | some n =>
        simp only [h,Option.map_some,Option.some.injEq] at observed
        subst value
        have small := ih n h
        change n/divisor < (limit input+divisor-1)/divisor
        have division := Nat.mod_add_div (limit input+divisor-1) divisor
        have remainder := Nat.mod_lt (limit input+divisor-1) positive
        apply (Nat.div_lt_iff_lt_mul positive).2
        rw [Nat.mul_comm]
        omega
    · cases observed

  | add left right modulus ihLeft ihRight =>
    cases hl : evaluate left with
    | none => simp only [evaluate,hl,Option.bind_none] at observed; cases observed
    | some a =>
      cases hr : evaluate right with
      | none => simp only [evaluate,hl,hr,Option.bind_some,Option.bind_none] at observed; cases observed
      | some b =>
        simp only [evaluate,hl,hr,Option.bind_some,Option.some.injEq] at observed
        subst value
        have al := ihLeft a hl
        have bl := ihRight b hr
        have reduced := Nat.mod_le (a+b) modulus
        change (a+b)%modulus < limit left+limit right-1
        omega
  | mul left right modulus ihLeft ihRight =>
    cases hl : evaluate left with
    | none => simp only [evaluate,hl,Option.bind_none] at observed; cases observed
    | some a =>
      cases hr : evaluate right with
      | none => simp only [evaluate,hl,hr,Option.bind_some,Option.bind_none] at observed; cases observed
      | some b =>
        simp only [evaluate,hl,hr,Option.bind_some,Option.some.injEq] at observed
        subst value
        have al := ihLeft a hl
        have bl := ihRight b hr
        have product := Nat.mul_le_mul (by omega : a ≤ limit left-1) (by omega : b ≤ limit right-1)
        have reduced := Nat.mod_le (a*b) modulus
        change (a*b)%modulus < (limit left-1)*(limit right-1)+1
        omega

def sourceEvent (expr : Expr) (slack : Nat) (effects : List (Result Unit)) :
    Result (Option IndexState) :=
  match evaluate expr with
  | none => .ok none
  | some index => through effects (some ⟨index,limit expr+slack⟩)

theorem event_guard (expr : Expr) (slack : Nat) (effects : List (Result Unit))
    (observed : IndexState) (ran : sourceEvent expr slack effects = .ok (some observed)) :
    indexGuard observed := by
  cases h : evaluate expr with
  | none => simp only [sourceEvent,h] at ran; cases ran
  | some index =>
    simp only [sourceEvent,h] at ran
    have frame := through_value _ _ _ ran
    cases frame
    have small := evaluate_bound expr index h
    change index < limit expr + slack
    omega

theorem event_certificate {α : Type} (expr : Expr) (slack : Nat) (effects : List (Result Unit))
    (observed : IndexState) (ran : sourceEvent expr slack effects = .ok (some observed))
    (normal first second : Result α) :
    ¬ diagnostic (indexGuard observed) ∧
      branch (indexGuard observed) normal first = branch (indexGuard observed) normal second :=
  (index_out_of_bounds observed normal first second).2 (event_guard expr slack effects observed ran)
#print axioms evaluate_bound
#print axioms event_guard
#print axioms event_certificate
end PV_B3P_ArithmeticEvents583227
