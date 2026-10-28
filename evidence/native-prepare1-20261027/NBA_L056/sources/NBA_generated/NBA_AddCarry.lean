import R1SamplerAddDigits
set_option autoImplicit false
namespace AspisR1.NBA_AddCarry
open SamplerAddDigits
abbrev P : Nat := 2147483647

def Frame (digit carry out next : Nat) : Prop :=
  out=(if digit+carry≥P then digit+carry-P else digit+carry) ∧
  next=(if digit+carry≥P then 1 else 0)

theorem step {digit carry out next : Nat} (hd : digit<P) (hc : carry≤257)
    (frame : Frame digit carry out next) :
    out=(digit+carry)%P ∧ next=(digit+carry)/P ∧ out<P ∧ next≤1 := by
  rcases frame with ⟨rfl,rfl⟩
  by_cases ge : digit+carry≥P
  · simp only [ge,↓reduceIte]
    dsimp only [P] at *
    omega
  · simp only [ge,↓reduceIte]
    dsimp only [P] at *
    omega

inductive Trace : List Nat → Nat → List Nat → Nat → Prop where
  | nil (carry : Nat) : Trace [] carry [] carry
  | cons (digit carry out next final : Nat) (xs ys : List Nat)
      (hd : digit<P) (hc : carry≤257) (frame : Frame digit carry out next)
      (tail : Trace xs next ys final) : Trace (digit::xs) carry (out::ys) final

theorem source {xs ys : List Nat} {carry final : Nat} (trace : Trace xs carry ys final) :
    addDigits P carry xs=(ys,final) := by
  induction trace with
  | nil carry => rfl
  | cons digit carry out next final xs ys hd hc frame tail ih =>
    have value := step hd hc frame
    simp only [addDigits,←value.1,←value.2.1,ih]

theorem unique {xs left right : List Nat} {carry a b : Nat}
    (lt : Trace xs carry left a) (rt : Trace xs carry right b) : left=right ∧ a=b := by
  have eqn := (source lt).symm.trans (source rt)
  exact ⟨congrArg Prod.fst eqn,congrArg Prod.snd eqn⟩

theorem construct (xs : List Nat) (carry : Nat) (hc : carry≤257)
    (canonical : ∀ d∈xs,d<P) : ∃ ys final, Trace xs carry ys final := by
  induction xs generalizing carry with
  | nil => exact ⟨[],carry,.nil carry⟩
  | cons d xs ih =>
    let out := if d+carry≥P then d+carry-P else d+carry
    let next := if d+carry≥P then 1 else 0
    have hd := canonical d (by simp)
    have frame : Frame d carry out next := ⟨rfl,rfl⟩
    have good := step hd hc frame
    obtain ⟨ys,final,tail⟩ := ih next (by omega) (fun d h => canonical d (by simp only [List.mem_cons]; exact Or.inr h))
    exact ⟨out::ys,final,.cons d carry out next final xs ys hd hc frame tail⟩

#print axioms step
#print axioms source
#print axioms unique
#print axioms construct
end AspisR1.NBA_AddCarry
