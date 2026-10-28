import R1Z.PV_RDB2D_SparseShape
namespace R1Z.PV_RDB2D_SparseLayout
open Aeneas Aeneas.Std Result R1Z.PV_RDB1_V183_ReserveWorld
open PV_RDB2D_CollectorTrace PV_RDB2D_SparseShape
set_option autoImplicit false

def shape : Shape := ⟨24,._Align1Shl3⟩
def empty (K : Type) : Buffer (Nat × K) := ⟨8,0,[],by rfl⟩
def request {K : Type} (isBoolean : K → Bool) (point : List K) : Request :=
  ⟨8,0,capacity isBoolean point,shape⟩

theorem public_layout {K : Type} (isBoolean : K → Bool) (point : List K) :
    publicRequest (request isBoolean point)=.allocate (24*capacity isBoolean point) 8 := by
  simp only [publicRequest,request,shape,alignmentWord,ite_true,Nat.mul_comm] <;> rfl

theorem padded : (24:Nat)%8=0 := rfl

theorem byte_bound {K : Type} (isBoolean : K → Bool) (point : List K)
    (length : point.length=10) : 24*capacity isBoolean point≤24576 := by
  have h := capacity_bound isBoolean point length
  omega

theorem nonzero {K : Type} (isBoolean : K → Bool) (point : List K) :
    0<24*capacity isBoolean point := Nat.mul_pos (by omega) (capacity_positive isBoolean point)

#print axioms public_layout
#print axioms padded
#print axioms byte_bound
#print axioms nonzero
end R1Z.PV_RDB2D_SparseLayout
