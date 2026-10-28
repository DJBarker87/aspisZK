-- Inherited body, import-only deployed-cohort retarget.
import NCD_B_LPi_RawValues
import NCD_B_LPi_FieldValues
set_option autoImplicit false
namespace AspisR1.LPi_CheckedInputs
open Aeneas Aeneas.Std Result LPi_FieldValues

def q (x : NQ) : FIo_Native.fast_pairing.canonical.Q :=
  Array.make 4#usize [x.c0.a,x.c0.b,x.c1.a,x.c1.b]

theorem canonical (x : NQ) (hx : canonQ x) : LPi_RawValues.Canon (q x) := by
  rcases hx with ⟨⟨h0,h1⟩,⟨h2,h3⟩⟩
  simp only [LPi_RawValues.Canon,q,Array.make,List.getElem!_cons_zero,List.getElem!_cons_succ]
  exact ⟨by omega,by omega,by omega,by omega⟩

theorem checked (x : NQ) (hx : canonQ x) :
    FIo_Native.fast_pairing.checked_q x=ok (.Ok (q x)) := by
  rcases hx with ⟨⟨h0,h1⟩,⟨h2,h3⟩⟩
  have l0 : x.c0.a < 2147483647#u32 := by scalar_tac
  have l1 : x.c0.b < 2147483647#u32 := by scalar_tac
  have l2 : x.c1.a < 2147483647#u32 := by scalar_tac
  have l3 : x.c1.b < 2147483647#u32 := by scalar_tac
  simp only [FIo_Native.fast_pairing.checked_q,FIo_Native.fast_pairing.limbs_of,
    bind_tc_ok,FIo_Native.fast_pairing.canonical.Q.from_limbs]
  simp [Array.index_usize,Array.make,FIo_Native.fast_pairing.canonical.P,
    h0,h1,h2,h3,q]

theorem from_wide (x : NE) : FIo_Native.fast_pairing.canonical.Q.from_wide x=
    ok (Array.make 2#usize [q x.c0,q x.c1]) := rfl

#print axioms canonical
#print axioms checked
#print axioms from_wide
end AspisR1.LPi_CheckedInputs
