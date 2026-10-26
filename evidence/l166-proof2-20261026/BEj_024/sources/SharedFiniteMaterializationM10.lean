import BinTypedWordDemandWork

/-! The returned closure captures the already constructed array. Its body
contains only one array access; materialization is outside the lambda. This
avoids assuming that partial application of readMaterialized hoists a table
construction out of each later query. -/
set_option autoImplicit false
namespace AspisR1.SharedFiniteMaterializationM10

def batch {A : Type} {n : Nat} (f : Fin n → A × Nat) : (Fin n → A) × Nat :=
  let table := Array.ofFn (fun i => (f i).1)
  (fun i => table[i.val]'(by have ht : table.size = n := Array.size_ofFn; omega),
    ((List.ofFn f).map Prod.snd).sum+3*n+1)

theorem value {A : Type} {n : Nat} (f : Fin n → A × Nat) (i : Fin n) :
    (batch f).1 i = (f i).1 := by
  simp only [batch, Array.getElem_ofFn]

theorem work {A : Type} {n : Nat} (f : Fin n → A × Nat) (C : Nat)
    (h : ∀ i, (f i).2 ≤ C) : (batch f).2 ≤ n*(C+3)+1 :=
  BinTypedWordDemandWork.materialize_work f C h

/-- Later array reads are individually annotated; batch construction is
already paid. The read body does not invoke f. -/
def read {A : Type} {n : Nat} (table : Fin n → A) (i : Fin n) : A × Nat :=
  (table i,1)

theorem read_value {A : Type} {n : Nat} (table : Fin n → A) (i : Fin n) :
    (read table i).1 = table i := rfl

theorem read_work {A : Type} {n : Nat} (table : Fin n → A) (i : Fin n) :
    (read table i).2 = 1 := rfl

#print axioms value
#print axioms work
#print axioms read_value
#print axioms read_work
end AspisR1.SharedFiniteMaterializationM10
