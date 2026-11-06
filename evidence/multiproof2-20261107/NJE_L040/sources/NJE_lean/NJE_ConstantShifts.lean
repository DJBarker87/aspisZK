import NJA_Internal

set_option autoImplicit false
namespace NJE_ConstantShifts

-- Literal INTERNAL_SHIFTS from frozen poseidon2.rs; sourcecheck pins bytes.
def source (i : Fin 15) : Nat := ![0,1,2,3,4,5,6,7,8,10,12,13,14,15,16] i

theorem model (i : Fin 15) : source i=R0P.poseidonInternalShifts i := by
 fin_cases i <;> rfl

theorem bound (i : Fin 15) : source i≤16 := by
 rw [model]
 exact NJA_Internal.shifts_bound i

#print model
#print axioms model
#print bound
#print axioms bound
end NJE_ConstantShifts
