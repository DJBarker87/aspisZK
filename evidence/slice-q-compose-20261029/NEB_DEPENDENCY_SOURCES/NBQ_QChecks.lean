import LPi_CheckedInputs
set_option autoImplicit false
namespace NBQ_QChecks
open Aeneas Aeneas.Std Result AspisR1 LPi_FieldValues

theorem from_limbs (a b c d : U32) :
    FIo_Native.fast_pairing.canonical.Q.from_limbs (Array.make 4#usize [a,b,c,d]) =
      ok (if a<2147483647#u32 ∧ b<2147483647#u32 ∧ c<2147483647#u32 ∧ d<2147483647#u32
        then some (Array.make 4#usize [a,b,c,d]) else none) := by
  simp only [FIo_Native.fast_pairing.canonical.Q.from_limbs,
    FIo_Native.fast_pairing.canonical.P,Array.index_usize,Array.make]
  split_ifs <;> simp_all

theorem checked_invalid (x : NQ) (bad : ¬canonQ x) :
    FIo_Native.fast_pairing.checked_q x=ok (.Err ()) := by
  have ck := from_limbs x.c0.a x.c0.b x.c1.a x.c1.b
  have invalid : ¬ (x.c0.a<2147483647#u32 ∧ x.c0.b<2147483647#u32 ∧
      x.c1.a<2147483647#u32 ∧ x.c1.b<2147483647#u32) := by
    intro h;apply bad;exact ⟨⟨by scalar_tac,by scalar_tac⟩,⟨by scalar_tac,by scalar_tac⟩⟩
  rw [if_neg invalid] at ck
  simp only [FIo_Native.fast_pairing.checked_q,FIo_Native.fast_pairing.limbs_of,bind_tc_ok,ck]

theorem push_invalid (s : FIo_Native.fast_pairing.EbyKDot) (v : NE) (x : NQ)
    (bad : ¬canonQ x) :
    FIo_Native.fast_pairing.EbyKDot.push s v x=ok (.Err (),s) := by
  by_cases cap : s.count ≥ FIo_Native.fast_pairing.MAX_TERMS
  · simp only [FIo_Native.fast_pairing.EbyKDot.push,if_pos cap]
  · simp only [FIo_Native.fast_pairing.EbyKDot.push,if_neg cap,
      LPi_CheckedInputs.from_wide,bind_tc_ok,checked_invalid x bad]
    rfl
#print axioms from_limbs
#print axioms checked_invalid
#print axioms push_invalid
end NBQ_QChecks
