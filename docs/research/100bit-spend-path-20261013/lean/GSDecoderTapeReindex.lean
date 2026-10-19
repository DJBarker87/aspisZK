import AspisV8R19.OracleResampling
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Data.Fintype.Pi

set_option autoImplicit false
namespace AspisR1.GSDecoderTapeReindex

abbrev RangeIndex (n : Nat) := {i : Nat // i ∈ Finset.range n}
abbrev Index (m n t : Nat) := (RangeIndex m ⊕ RangeIndex n) × Fin t
abbrev BankTape (K : Type) (m n t : Nat) :=
  (RangeIndex m → Fin t → K × K) × (RangeIndex n → Fin t → K × K)

def rangeFin (n : Nat) : RangeIndex n ≃ Fin n where
  toFun i := ⟨i.1, Finset.mem_range.mp i.2⟩
  invFun i := ⟨i.1, Finset.mem_range.mpr i.2⟩
  left_inv i := by apply Subtype.ext; rfl
  right_inv i := by apply Fin.ext; rfl

def indexFin (m n t : Nat) : Index m n t ≃ Fin ((m+n)*t) :=
  (Equiv.prodCongr
    ((Equiv.sumCongr (rangeFin m) (rangeFin n)).trans finSumFinEquiv)
    (Equiv.refl (Fin t))).trans finProdFinEquiv

def indexedBank (K : Type) (m n t : Nat) :
    (Index m n t → K × K) ≃ BankTape K m n t where
  toFun f := (fun i j => f (Sum.inl i,j), fun i j => f (Sum.inr i,j))
  invFun H p := Sum.elim (fun i => H.1 i p.2) (fun i => H.2 i p.2) p.1
  left_inv f := by
    funext p
    rcases p with ⟨i,j⟩
    cases i <;> rfl
  right_inv H := rfl

/-- A concrete reindexing only: no field enumeration, rejection or additional
randomness occurs here. The two groups will be shared across decoder calls. -/
def flatBank (K : Type) (m n t : Nat) :
    (Fin ((m+n)*t) → K × K) ≃ BankTape K m n t :=
  (Equiv.arrowCongr (indexFin m n t).symm (Equiv.refl (K × K))).trans
    (indexedBank K m n t)

noncomputable section
open AspisV8R19.OracleResampling

theorem mean_flatBank {K : Type} [Fintype K] (m n t : Nat)
    (f : BankTape K m n t → ℚ) :
    mean (fun H : Fin ((m+n)*t) → K × K => f (flatBank K m n t H)) = mean f :=
  mean_equiv (flatBank K m n t) f

/-- Number of sampled pairs for the maintained public bounds and 149 retries.
Sharing these two tapes across all fixed input calls does not multiply this
count by the number of calls. -/
theorem concrete_pair_positions : ((1025*112 + 256*112)*149 : Nat) = 21377328 := by
  norm_num

#print axioms rangeFin
#print axioms indexFin
#print axioms indexedBank
#print axioms flatBank
#print axioms mean_flatBank
#print axioms concrete_pair_positions
end
end AspisR1.GSDecoderTapeReindex
