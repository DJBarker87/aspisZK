import R1Z.SimCostCollect5
import R1Z.SimCostView

/-! WideExact addition on materialized coordinate arrays, and the exact
cardinality of the actual R1 payload. The array algorithm has a cost proof;
cardinality alone is not an implementation of payload serialization or of
the reference/mask/shift formulas. -/
set_option autoImplicit false
noncomputable section
namespace R1Z.SimCostFormula5
open AspisWideTower R1Z.SimCostWriter R0Z.HonestView R1Z.Batched R1Z.SimCostCollect5
attribute [local irreducible] collect

def arrayAdd (n : Nat) (p : (Fin n → WideExact) × (Fin n → WideExact)) :=
  collect n (fun i => bind (tick 2) fun _ => SimCostWide5.add.run (p.1 i,p.2 i))

theorem arrayAdd_erase (n : Nat) (p : (Fin n → WideExact) × (Fin n → WideExact)) :
    (arrayAdd n p).1 = p.1+p.2 := by
  simp only [arrayAdd, collect_erase, erase_bind, SimCostWide5.add.erase]
  rfl

theorem arrayAdd_bound (n : Nat) (p : (Fin n → WideExact) × (Fin n → WideExact)) :
    (arrayAdd n p).2 ≤ 14*n := by
  apply (collect_bound n 12 _ ?_).trans
  · omega
  · intro i
    simp only [cost_bind, tick, SimCostWide5.add, SimCostWide5.add_cost]
    exact Nat.le_refl _

/-- Explicit finite shape; neither its universe nor its elements are reduced. -/
def payloadEquiv : PayloadCell R1Bat ≃
    Unit ⊕ ((Fin 10 × Fin 28) ⊕ ((Fin 3 × Fin 29) ⊕
      (Fin 29 ⊕ ((Fin 2 × Fin 29) ⊕ (Unit ⊕
        ((Fin 262144 × Fin 4 × Fin 29) ⊕ R1Bat)))))) where
  toFun
    | .maskSum => .inl ()
    | .semanticCoeff j i => .inr (.inl (j,i))
    | .pointClaim j i => .inr (.inr (.inl (j,i)))
    | .extraClaim i => .inr (.inr (.inr (.inl i)))
    | .ood j i => .inr (.inr (.inr (.inr (.inl (j,i)))))
    | .inactiveSum => .inr (.inr (.inr (.inr (.inr (.inl ())))))
    | .opened q s c => .inr (.inr (.inr (.inr (.inr (.inr (.inl (q,s,c)))))))
    | .bat i => .inr (.inr (.inr (.inr (.inr (.inr (.inr i))))))
  invFun
    | .inl _ => .maskSum
    | .inr (.inl (j,i)) => .semanticCoeff j i
    | .inr (.inr (.inl (j,i))) => .pointClaim j i
    | .inr (.inr (.inr (.inl i))) => .extraClaim i
    | .inr (.inr (.inr (.inr (.inl (j,i))))) => .ood j i
    | .inr (.inr (.inr (.inr (.inr (.inl _))))) => .inactiveSum
    | .inr (.inr (.inr (.inr (.inr (.inr (.inl (q,s,c))))))) => .opened q s c
    | .inr (.inr (.inr (.inr (.inr (.inr (.inr i)))))) => .bat i
  left_inv c := by cases c <;> rfl
  right_inv c := by
    rcases c with u | c
    · cases u; rfl
    rcases c with ⟨j,i⟩ | c
    · rfl
    rcases c with ⟨j,i⟩ | c
    · rfl
    rcases c with i | c
    · rfl
    rcases c with ⟨j,i⟩ | c
    · rfl
    rcases c with u | c
    · cases u; rfl
    rcases c with ⟨q,s,c⟩ | i <;> rfl

theorem payload_nat_card : Nat.card (PayloadCell R1Bat) = 30671382 := by
  have hb : Nat.card R1Bat = 262222 := by
    calc
      Nat.card R1Bat = Nat.card ((Fin 7 ⊕ Fin 7) ⊕ (Fin 262144 ⊕ Fin 64)) :=
        Nat.card_congr R1Bat.equivSum
      _ = 262222 := by simp only [Nat.card_sum, Nat.card_fin]
  calc
    Nat.card (PayloadCell R1Bat) = Nat.card
      (Unit ⊕ ((Fin 10 × Fin 28) ⊕ ((Fin 3 × Fin 29) ⊕
        (Fin 29 ⊕ ((Fin 2 × Fin 29) ⊕ (Unit ⊕
          ((Fin 262144 × Fin 4 × Fin 29) ⊕ R1Bat))))))) := Nat.card_congr payloadEquiv
    _ = 30671382 := by
      simp only [Nat.card_sum, Nat.card_prod, Nat.card_fin, hb,
        Nat.card_eq_fintype_card (α := Unit), Fintype.card_unit]

theorem payload_card : Fintype.card (PayloadCell R1Bat) = 30671382 :=
  (Nat.card_eq_fintype_card.symm).trans payload_nat_card

/-- Worst-case loop bound for arrays with exactly one entry for every actual
payload cell. The separate representation/encoding bridge is not assumed. -/
theorem full_array_add_bound
    (p : (Fin 30671382 → WideExact) × (Fin 30671382 → WideExact)) :
    (arrayAdd 30671382 p).2 ≤ 429399348 :=
  arrayAdd_bound 30671382 p

#print axioms arrayAdd_erase
#print axioms arrayAdd_bound
#print axioms payloadEquiv
#print axioms payload_nat_card
#print axioms payload_card
#print axioms full_array_add_bound
end R1Z.SimCostFormula5
