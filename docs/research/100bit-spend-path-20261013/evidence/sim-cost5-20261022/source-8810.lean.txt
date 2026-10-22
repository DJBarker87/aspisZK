import R1Z.SimCostWide5

/-! Complete payload addition by explicit structural traversal. All coordinates,
including the public zero extension of unopened cells, are included. No
Finset.univ is reduced. Reads of two supplied coordinates cost two RAM ticks;
this is not a cost certificate for evaluating arbitrary input functions. -/
set_option autoImplicit false
noncomputable section
namespace R1Z.SimCostCollect5
open AspisWideTower R1Z.SimCostWriter R0Z.HonestView R1Z.Batched

def collect {A : Type} : (n : Nat) → (Fin n → Costed A) → Costed (Fin n → A)
  | 0, _ => (Fin.elim0,0)
  | n+1, f =>
    bind (f 0) fun head =>
    bind (collect n (fun i => f i.succ)) fun tail => (Fin.cons head tail,2)

theorem collect_erase {A : Type} (n : Nat) (f : Fin n → Costed A) :
    (collect n f).1 = fun i => (f i).1 := by
  induction n with
  | zero => funext i; exact Fin.elim0 i
  | succ n ih =>
    simp only [collect, erase_bind, ih]
    funext i
    refine Fin.cases ?_ (fun j => ?_) i <;> rfl

theorem collect_bound {A : Type} (n c : Nat) (f : Fin n → Costed A)
    (hf : ∀ i, (f i).2 ≤ c) : (collect n f).2 ≤ n*(c+2) := by
  induction n with
  | zero => simp only [collect, Nat.zero_mul, le_refl]
  | succ n ih =>
    have hh := hf 0
    have ht := ih (fun i => f i.succ) (fun i => hf i.succ)
    simp only [collect, cost_bind]
    nlinarith

def collect2 {A : Type} (n m : Nat) (f : Fin n → Fin m → Costed A) :=
  collect n (fun i => collect m (f i))

theorem collect2_erase {A : Type} (n m : Nat) (f : Fin n → Fin m → Costed A) :
    (collect2 n m f).1 = fun i j => (f i j).1 := by
  simp only [collect2, collect_erase]

theorem collect2_bound {A : Type} (n m c : Nat) (f : Fin n → Fin m → Costed A)
    (hf : ∀ i j, (f i j).2 ≤ c) :
    (collect2 n m f).2 ≤ n*(m*(c+2)+2) :=
  collect_bound n _ _ (fun i => collect_bound m c (f i) (hf i))

def collect3 {A : Type} (n m k : Nat) (f : Fin n → Fin m → Fin k → Costed A) :=
  collect n (fun i => collect2 m k (f i))

theorem collect3_erase {A : Type} (n m k : Nat)
    (f : Fin n → Fin m → Fin k → Costed A) :
    (collect3 n m k f).1 = fun i j l => (f i j l).1 := by
  simp only [collect3, collect_erase, collect2_erase]

theorem collect3_bound {A : Type} (n m k c : Nat)
    (f : Fin n → Fin m → Fin k → Costed A) (hf : ∀ i j l, (f i j l).2 ≤ c) :
    (collect3 n m k f).2 ≤ n*(m*(k*(c+2)+2)+2) :=
  collect_bound n _ _ (fun i => collect2_bound m k c (f i) (hf i))

#print axioms collect_erase
#print axioms collect_bound
#print axioms collect2_erase
#print axioms collect2_bound
#print axioms collect3_erase
#print axioms collect3_bound
end R1Z.SimCostCollect5
