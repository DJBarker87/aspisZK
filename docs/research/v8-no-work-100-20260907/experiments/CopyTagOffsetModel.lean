import CopyTagSplit

namespace AspisV8.CopyTagOffset
open AspisV8.CopyTagSplit

-- The instruction vocabulary emitted by the new generator. Coefficients and
-- selector indices are bounded in the type; no received field is enumerated.
inductive Plan where
  | zero
  | term (index : Fin 64) (coefficient : Fin 136)
  | add (left right : Plan)

def eval (h : Fin 64 → Nat) : Plan → Nat
  | .zero => 0
  | .term i c => h i*c.val
  | .add l r => eval h l + eval h r

def count : Plan → Nat
  | .zero => 0
  | .term _ _ => 1
  | .add l r => count l+count r

def machine (h : Fin 64 → Nat) : Plan → Nat
  | .zero => 0
  | .term i c => (h i*c.val)%(2^64)
  | .add l r => (machine h l + machine h r)%(2^64)

theorem zero_plan (h : Fin 64 → Nat) : eval h .zero = 0 := rfl

theorem machine_eq_mod (h : Fin 64 → Nat) (t : Plan) :
    machine h t = eval h t % (2^64) := by
  induction t with
  | zero => rfl
  | term i c => rfl
  | add l r hl hr =>
    simp only [machine,eval,hl,hr]
    exact (Nat.add_mod (eval h l) (eval h r) (2^64)).symm

theorem eval_bound (h : Fin 64 → Nat) (hh : ∀ i, h i < p) (t : Plan) :
    eval h t ≤ count t * ((p-1)*135) := by
  induction t with
  | zero => simp [eval,count]
  | term i c =>
    simp only [eval,count,Nat.one_mul]
    exact Nat.mul_le_mul (by have hi := hh i; omega) (by omega)
  | add l r hl hr =>
    simp only [eval,count,Nat.add_mul]
    exact Nat.add_le_add hl hr

theorem complete_raw_bound (h : Fin 64 → Nat) (hh : ∀ i, h i < p)
    (t : Plan) (hn : count t ≤ 272) : eval h t ≤ 78855599481120 := by
  have hb := eval_bound h hh t
  have hm := Nat.mul_le_mul_right ((p-1)*135) hn
  norm_num [p] at hb hm
  omega

theorem machine_exact (h : Fin 64 → Nat) (hh : ∀ i, h i < p)
    (t : Plan) (hn : count t ≤ 272) : machine h t = eval h t := by
  rw [machine_eq_mod]
  apply Nat.mod_eq_of_lt
  have hb := complete_raw_bound h hh t hn
  omega

-- Bounds every child computation, not only a final reduced result.
def allBounded (bound : Nat) (h : Fin 64 → Nat) : Plan → Prop
  | .zero => 0 ≤ bound
  | .term i c => h i*c.val ≤ bound
  | .add l r => eval h (.add l r) ≤ bound ∧ allBounded bound h l ∧ allBounded bound h r

theorem all_intermediates_bounded (bound : Nat) (h : Fin 64 → Nat) (t : Plan)
    (hb : eval h t ≤ bound) : allBounded bound h t := by
  induction t with
  | zero => exact hb
  | term i c => exact hb
  | add l r hl hr =>
    refine ⟨hb,hl ?_,hr ?_⟩ <;> simp only [eval] at hb <;> omega

#print axioms zero_plan
#print axioms machine_eq_mod
#print axioms eval_bound
#print axioms complete_raw_bound
#print axioms machine_exact
#print axioms all_intermediates_bounded
end AspisV8.CopyTagOffset
