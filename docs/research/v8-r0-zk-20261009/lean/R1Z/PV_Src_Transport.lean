import R1Z.BuilderTransport
import R1Z.BuilderSource

/-! The transport computed by the extracted arithmetic reference, with
success and bounds proved before constructing the finite equivalence.
The shipped bitwise callee association is deliberately not inferred here. -/
set_option autoImplicit false
namespace R1Z.PV_Src_Transport
open Aeneas Aeneas.Std Result R0Z.WriterRefine

def index (j : Fin 1024) : Usize := UScalar.ofNatCore j.val (by scalar_tac)

theorem index_val (j : Fin 1024) : (index j).val = j.val :=
  UScalar.ofNatCore_val_eq _

def rawRow (j : Fin 1024) : Usize := okOr (AspisBuilderReference.row_arithmetic (index j)) 0#usize

theorem rawRow_val (j : Fin 1024) : (rawRow j).val = AspisR1.rowNat j.val := by
  obtain ⟨out,ho,hv⟩ := BuilderTransport.reference_row (index j)
  rw [index_val] at hv
  rw [rawRow,ho,okOr_ok]
  exact hv

theorem row_success (j : Fin 1024) :
    AspisBuilderReference.row_arithmetic (index j) = ok (rawRow j) := by
  obtain ⟨out,ho,_⟩ := BuilderTransport.reference_row (index j)
  rw [rawRow,ho,okOr_ok]

def row (j : Fin 1024) : Fin 1024 :=
  ⟨(rawRow j).val,by rw [rawRow_val]; exact AspisR1.rowNat_lt _⟩

theorem row_eq (j : Fin 1024) : row j = AspisR1.row j := Fin.ext (rawRow_val j)

def transport : Fin 1024 ≃ Fin 1024 where
  toFun := row
  invFun := row
  left_inv := by intro j; rw [row_eq,row_eq]; exact AspisR1.row_involutive j
  right_inv := by intro j; rw [row_eq,row_eq]; exact AspisR1.row_involutive j

theorem transport_eq : transport = BuilderSource.π := by
  apply Equiv.ext
  exact row_eq

#print axioms index_val
#print axioms rawRow_val
#print axioms row_success
#print axioms row_eq
#print axioms transport_eq
end R1Z.PV_Src_Transport
