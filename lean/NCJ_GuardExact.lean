import NCJ_QEquality
set_option autoImplicit false
noncomputable section
namespace NCJ_GuardExact
open Aeneas Aeneas.Std Result FIo_Native
attribute [local instance] Classical.propDecidable

def pick {α : Type} {n : Usize} (a : Array α n) (i : Nat) (h : i<n.val) : α :=
  a.val[i]'(by rw [a.property];exact h)

theorem index {α : Type} {n : Usize} (a : Array α n) (i : Usize) (h : i.val<n.val) :
    Array.index_usize a i = ok (pick a i.val h) := by
  simp [Array.index_usize,pick,h]

def row (w : weights.Weights) (k : Fin 5) (d : Fin 5) :=
  pick (pick w.factors k.val k.isLt) d.val d.isLt

def guard (w : weights.Weights) (folds : Usize) : Bool :=
  decide (w.variant = .S2 ∧ folds=2#usize ∧ row w 0 2 = row w 2 2 ∧ row w 0 3=row w 2 3)

theorem source (w : weights.Weights) (folds : Usize) :
    weights.shared_two_point_guard w folds = ok (guard w folds) := by
  cases hv : w.variant <;>
    simp [weights.shared_two_point_guard,
      transport.Variant.Insts.CoreCmpPartialEqVariant.eq,
      transport.Variant.read_discriminant,hv,guard,index,row,NCJ_QEquality.arrays]
  repeat' split <;> simp_all

#print axioms index
#print axioms source
end NCJ_GuardExact
