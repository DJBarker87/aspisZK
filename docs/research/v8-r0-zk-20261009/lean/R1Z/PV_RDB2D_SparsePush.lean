import R1Z.PV_RDB2D_SparseEntries
import R1Z.PV_RDB2D_SparseReserve
namespace R1Z.PV_RDB2D_SparsePush
open Aeneas Aeneas.Std Result PV_RDB1_V183_ReserveWorld
set_option autoImplicit false

def buffer {K : Type} (address cap : Nat) (entries : List K) (length : entries.length=cap) (i : Nat) : Buffer K :=
  ⟨address,cap,entries.take i,by rw [List.length_take,length];exact Nat.min_le_right _ _⟩

theorem no_reallocation {K S F : Type} (step : Request → S → Option Nat × S)
    (shape : Shape) (address cap : Nat) (entries : List K) (length : entries.length=cap)
    (i : Nat) (active : i<cap) (world : World S F) (wordMax byteMax : Nat) :
    native step wordMax byteMax shape (buffer address cap entries length i) 1 world=
      ⟨.ok (),buffer address cap entries length i,world⟩ := by
  apply no_growth
  change 1≤cap-(entries.take i).length
  rw [List.length_take,length,Nat.min_eq_left (by omega)]
  omega

#print axioms no_reallocation
end R1Z.PV_RDB2D_SparsePush
