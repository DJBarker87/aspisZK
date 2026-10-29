import R1Z.PV_RDB2D_SparseAddress
namespace R1Z.PV_RDB2D_SparseLookup
open Aeneas Aeneas.Std Result
set_option autoImplicit false

def read {K : Type} (column : List K) (row : Nat) : Result K :=
  match column[row]? with
  | none => fail .arrayOutOfBounds
  | some value => ok value

theorem present {K : Type} (column : List K) (row : Nat) (h : row<column.length) :
    read column row=ok (column[row]'h) := by
  simp only [read,List.getElem?_eq_getElem h]

theorem absent {K : Type} (column : List K) (row : Nat) (h : column.length≤row) :
    read column row=fail .arrayOutOfBounds := by
  simp only [read,List.getElem?_eq_none h]

theorem sparse_present {K : Type} (column : List K) (length : column.length=1024)
    (width trailing suffix pref : Nat) (split : width+trailing=10)
    (hs : suffix<2^trailing) (hp : pref<2^width) :
    ∃ value, read column (PV_RDB2D_SparseAddress.row pref trailing suffix)=ok value := by
  have h := PV_RDB2D_SparseAddress.bound width trailing suffix pref split hs hp
  have bound : PV_RDB2D_SparseAddress.row pref trailing suffix<column.length := by omega
  exact ⟨column[_]'bound,present column _ bound⟩

#print axioms present
#print axioms absent
#print axioms sparse_present
end R1Z.PV_RDB2D_SparseLookup
