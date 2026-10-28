import NCJ_TensorDomains
set_option autoImplicit false
namespace NCJ_TensorFrame

def write {R : Type} (out : Nat → R) (i : Nat) (v : R) : Nat → R :=
  fun k => if k=i then v else out k

def place {R : Type} (n j : Nat) (r : Fin 4 → R) (out : Nat → R) : Nat → R :=
  write (write (write (write out j (r 0)) (j+n) (r 1)) (j+2*n) (r 2)) (j+3*n) (r 3)

theorem frame {R : Type} (n j i : Nat) (r : Fin 4 → R) (out : Nat → R)
    (h : ∀ lane : Fin 4, i≠j+lane.val*n) : place n j r out i = out i := by
  have h0:=h 0;have h1:=h 1;have h2:=h 2;have h3:=h 3
  simpa [place,write] using (show (if i=j+3*n then r 3 else
    if i=j+2*n then r 2 else if i=j+n then r 1 else if i=j then r 0 else out i)=out i by
      simp_all)

theorem selected {R : Type} (n j : Nat) (r : Fin 4 → R) (out : Nat → R)
    (hn : 0<n) (lane : Fin 4) : place n j r out (j+lane.val*n) = r lane := by
  have hl:=lane.isLt
  have cases : lane=0 ∨ lane=1 ∨ lane=2 ∨ lane=3 := by
    have : lane.val=0 ∨ lane.val=1 ∨ lane.val=2 ∨ lane.val=3 := by omega
    rcases this with h|h|h|h
    · exact Or.inl (Fin.ext h)
    · exact Or.inr (Or.inl (Fin.ext h))
    · exact Or.inr (Or.inr (Or.inl (Fin.ext h)))
    · exact Or.inr (Or.inr (Or.inr (Fin.ext h)))
  rcases cases with rfl|rfl|rfl|rfl <;> simp [place,write] <;> split <;> omega

def descend {R : Type} (n : Nat) (f : Nat → R → Fin 4 → R) : Nat → (Nat → R) → Nat → R
  | 0,out => out
  | m+1,out => descend n f m (place n m (f m (out m)) out)

theorem descend_frame {R : Type} (n : Nat) (f : Nat → R → Fin 4 → R)
    (m i : Nat) (out : Nat → R)
    (h : ∀ j, j<m → ∀ lane : Fin 4, i≠j+lane.val*n) :
    descend n f m out i = out i := by
  induction m generalizing out with
  | zero => rfl
  | succ m ih =>
    simp only [descend]
    rw [ih _ (fun j hj => h j (by omega)),frame]
    exact h m (by omega)

/-- Descending expansion reads each original coefficient before overwriting
its four lanes. The arbitrary reply function can be instantiated by the
Lean-discharged multiplication specification after native logging. -/
theorem descend_selected {R : Type} (n : Nat) (hn : NCJ_TensorDomains.Stage n)
    (f : Nat → R → Fin 4 → R) (m : Nat) (hm : m≤n) (out : Nat → R)
    (j : Nat) (hj : j<m) (lane : Fin 4) :
    descend n f m out (j+lane.val*n) = f j (out j) lane := by
  induction m generalizing out with
  | zero => omega
  | succ m ih =>
    simp only [descend]
    by_cases same : j=m
    · subst j
      rw [descend_frame n f m (m+lane.val*n) _ ?_,selected]
      · exact NCJ_TensorDomains.positive n hn
      · intro i hi other
        exact Ne.symm (NCJ_TensorDomains.writes_disjoint n i m other.val lane.val hn
          (by omega) (by omega) other.isLt lane.isLt (by omega))
    · have before : j<m := by omega
      rw [ih (by omega) _ before]
      have read : place n m (f m (out m)) out j=out j := by
        apply frame
        intro other
        exact NCJ_TensorDomains.unread_frame n m j other.val hn (by omega) before other.isLt
      rw [read]

#print axioms frame
#print axioms selected
#print axioms descend_frame
#print axioms descend_selected
end NCJ_TensorFrame
