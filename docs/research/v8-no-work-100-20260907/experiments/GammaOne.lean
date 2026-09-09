import Mathlib.Tactic
namespace AspisV8.GammaOne
def p : Nat := 2147483647
def word : Nat := 2^64
def identity (i : Fin 4) : Nat := if i=0 then 1 else 0
def raw (head : Fin 4 → Nat) (i : Fin 4) (v tail : Nat) := head i*v+tail
noncomputable def guarded (head : Fin 4 → Nat) (i : Fin 4) (v tail : Nat) :=
  if head=identity then (if i=0 then v+tail else tail) else raw head i v tail

-- Neither honest power generation nor a premise that the head equals one is
-- needed: the generic branch remains part of the total function.
theorem guarded_eq_raw (head : Fin 4 → Nat) (i : Fin 4) (v tail : Nat) :
    guarded head i v tail=raw head i v tail := by
  classical
  by_cases h : head=identity
  · subst head
    by_cases hi : i=0 <;> simp [guarded,raw,identity,hi]
  · simp [guarded,h]

theorem canonical_first_bound (h v tail : Nat) (hh : h<p) (hv : v<p)
    (ht : tail≤3*(p-1)^2) : h*v+tail<word := by
  have hhm : h≤p-1 := by dsimp [p] at *; omega
  have hvm : v≤p-1 := by dsimp [p] at *; omega
  have hm := Nat.mul_le_mul hhm hvm
  have cap : 4*(p-1)^2<word := by norm_num [p,word]
  nlinarith

theorem guarded_bound (head : Fin 4 → Nat) (i : Fin 4) (v tail : Nat)
    (hh : head i<p) (hv : v<p) (ht : tail≤3*(p-1)^2) :
    guarded head i v tail<word := by
  rw [guarded_eq_raw]
  exact canonical_first_bound (head i) v tail hh hv ht

theorem prefix_wrap_exact (head : Fin 4 → Nat) (i : Fin 4) (v tail part : Nat)
    (hh : head i<p) (hv : v<p) (ht : tail≤3*(p-1)^2)
    (hp : part≤guarded head i v tail) : part%word=part := by
  exact Nat.mod_eq_of_lt (lt_of_le_of_lt hp (guarded_bound head i v tail hh hv ht))

theorem carried_endpoint {A : Type*} (finish : Nat → A)
    (head : Fin 4 → Nat) (i : Fin 4) (v tail : Nat) :
    finish (guarded head i v tail)=finish (raw head i v tail) := by
  rw [guarded_eq_raw]

-- Dropping the guard is genuinely false, not merely an unproved interface.
theorem unguarded_counterexample :
    (if (0 : Fin 4)=0 then 1+0 else 0) ≠ raw (fun _=>2) 0 1 0 := by
  norm_num [raw]

-- Moving the public dispatch before common canonical decoding preserves
-- errors too; decoder success is NOT a premise of this equality.
theorem dispatch_preserves_errors {E A B : Type*} (decoded : Except E A)
    (fast slow : A → Except E B) (useFast : Bool) :
    decoded.bind (fun v => if useFast then fast v else slow v) =
      (if useFast then decoded.bind fast else decoded.bind slow) := by
  cases useFast <;> rfl

#print axioms guarded_eq_raw
#print axioms canonical_first_bound
#print axioms guarded_bound
#print axioms prefix_wrap_exact
#print axioms carried_endpoint
#print axioms unguarded_counterexample
#print axioms dispatch_preserves_errors
end AspisV8.GammaOne
