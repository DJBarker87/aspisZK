import FIp_PowersState
set_option autoImplicit false
noncomputable section
namespace AspisR1.FIp_PowersWrite
open Aeneas Aeneas.Std Result AspisR1CurrentWide.Proof
open FIo_FieldBridge (NE wide)
open FIp_PowersState

theorem written {N : Usize} (x p : NE) (a : Array NE N) (i : Usize)
    (old : NE) (back : NE → Array NE N)
    (run : Array.index_mut_usize a i=ok (old,back))
    (hi : i.val<N.val)
    (hp : decodeWide (wide p)=decodeWide (wide x)^i.val)
    (values : ∀ j,j<i.val → FIp_ArrayValue.value a j=decodeWide (wide x)^j) :
    ∀ j,j<i.val+1 → FIp_ArrayValue.value (back p) j=decodeWide (wide x)^j := by
  rw [FIp_ArraySetValue.back a i old back run]
  intro j hj
  by_cases same : j=i.val
  · subst j
    rw [FIp_ArraySetValue.same a i p hi]
    exact hp
  · rw [FIp_ArraySetValue.other a i p j (Ne.symm same)]
    exact values j (by omega)

#print axioms written
end AspisR1.FIp_PowersWrite
end
