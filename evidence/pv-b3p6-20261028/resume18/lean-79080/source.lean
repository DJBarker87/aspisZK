import PV_B3P_FromFnFour550227
import PV_B3P_P227_02
import PV_B3P_DigestCpsEq9227
import Lean.Elab.Tactic.AsAuxLemma
namespace PV_B3P_Association554227
open Aeneas Aeneas.Std PV_B3P_227 Result PV_B3P_Binding9227 PV_B3P_Association550227
set_option autoImplicit false

def external_sums_source554 (state : Array aspis_core.field.QM31 16#usize) :
    Result (Array (Array U64 4#usize) 4#usize) := do
  let q0_0 ← Array.index_usize state 0#usize
  let a0_0_0 ← reference_poseidon.extension_limbs q0_0
  let b0_0_0 ← Array.index_usize a0_0_0 0#usize
  let c0_0_0 ← lift (core.convert.num.FromU64U32.from b0_0_0)
  let q0_1 ← Array.index_usize state 4#usize
  let a0_0_1 ← reference_poseidon.extension_limbs q0_1
  let b0_0_1 ← Array.index_usize a0_0_1 0#usize
  let c0_0_1 ← lift (core.convert.num.FromU64U32.from b0_0_1)
  let sum0_0_1 ← lift (U64.wrapping_add c0_0_0 c0_0_1)
  let q0_2 ← Array.index_usize state 8#usize
  let a0_0_2 ← reference_poseidon.extension_limbs q0_2
  let b0_0_2 ← Array.index_usize a0_0_2 0#usize
  let c0_0_2 ← lift (core.convert.num.FromU64U32.from b0_0_2)
  let sum0_0_2 ← lift (U64.wrapping_add sum0_0_1 c0_0_2)
  let q0_3 ← Array.index_usize state 12#usize
  let a0_0_3 ← reference_poseidon.extension_limbs q0_3
  let b0_0_3 ← Array.index_usize a0_0_3 0#usize
  let c0_0_3 ← lift (core.convert.num.FromU64U32.from b0_0_3)
  let sum0_0_3 ← lift (U64.wrapping_add sum0_0_2 c0_0_3)
  let a0_1_0 ← reference_poseidon.extension_limbs q0_0
  let b0_1_0 ← Array.index_usize a0_1_0 1#usize
  let c0_1_0 ← lift (core.convert.num.FromU64U32.from b0_1_0)
  let a0_1_1 ← reference_poseidon.extension_limbs q0_1
  let b0_1_1 ← Array.index_usize a0_1_1 1#usize
  let c0_1_1 ← lift (core.convert.num.FromU64U32.from b0_1_1)
  let sum0_1_1 ← lift (U64.wrapping_add c0_1_0 c0_1_1)
  let a0_1_2 ← reference_poseidon.extension_limbs q0_2
  let b0_1_2 ← Array.index_usize a0_1_2 1#usize
  let c0_1_2 ← lift (core.convert.num.FromU64U32.from b0_1_2)
  let sum0_1_2 ← lift (U64.wrapping_add sum0_1_1 c0_1_2)
  let a0_1_3 ← reference_poseidon.extension_limbs q0_3
  let b0_1_3 ← Array.index_usize a0_1_3 1#usize
  let c0_1_3 ← lift (core.convert.num.FromU64U32.from b0_1_3)
  let sum0_1_3 ← lift (U64.wrapping_add sum0_1_2 c0_1_3)
  let a0_2_0 ← reference_poseidon.extension_limbs q0_0
  let b0_2_0 ← Array.index_usize a0_2_0 2#usize
  let c0_2_0 ← lift (core.convert.num.FromU64U32.from b0_2_0)
  let a0_2_1 ← reference_poseidon.extension_limbs q0_1
  let b0_2_1 ← Array.index_usize a0_2_1 2#usize
  let c0_2_1 ← lift (core.convert.num.FromU64U32.from b0_2_1)
  let sum0_2_1 ← lift (U64.wrapping_add c0_2_0 c0_2_1)
  let a0_2_2 ← reference_poseidon.extension_limbs q0_2
  let b0_2_2 ← Array.index_usize a0_2_2 2#usize
  let c0_2_2 ← lift (core.convert.num.FromU64U32.from b0_2_2)
  let sum0_2_2 ← lift (U64.wrapping_add sum0_2_1 c0_2_2)
  let a0_2_3 ← reference_poseidon.extension_limbs q0_3
  let b0_2_3 ← Array.index_usize a0_2_3 2#usize
  let c0_2_3 ← lift (core.convert.num.FromU64U32.from b0_2_3)
  let sum0_2_3 ← lift (U64.wrapping_add sum0_2_2 c0_2_3)
  let a0_3_0 ← reference_poseidon.extension_limbs q0_0
  let b0_3_0 ← Array.index_usize a0_3_0 3#usize
  let c0_3_0 ← lift (core.convert.num.FromU64U32.from b0_3_0)
  let a0_3_1 ← reference_poseidon.extension_limbs q0_1
  let b0_3_1 ← Array.index_usize a0_3_1 3#usize
  let c0_3_1 ← lift (core.convert.num.FromU64U32.from b0_3_1)
  let sum0_3_1 ← lift (U64.wrapping_add c0_3_0 c0_3_1)
  let a0_3_2 ← reference_poseidon.extension_limbs q0_2
  let b0_3_2 ← Array.index_usize a0_3_2 3#usize
  let c0_3_2 ← lift (core.convert.num.FromU64U32.from b0_3_2)
  let sum0_3_2 ← lift (U64.wrapping_add sum0_3_1 c0_3_2)
  let a0_3_3 ← reference_poseidon.extension_limbs q0_3
  let b0_3_3 ← Array.index_usize a0_3_3 3#usize
  let c0_3_3 ← lift (core.convert.num.FromU64U32.from b0_3_3)
  let sum0_3_3 ← lift (U64.wrapping_add sum0_3_2 c0_3_3)
  let q1_0 ← Array.index_usize state 1#usize
  let a1_0_0 ← reference_poseidon.extension_limbs q1_0
  let b1_0_0 ← Array.index_usize a1_0_0 0#usize
  let c1_0_0 ← lift (core.convert.num.FromU64U32.from b1_0_0)
  let q1_1 ← Array.index_usize state 5#usize
  let a1_0_1 ← reference_poseidon.extension_limbs q1_1
  let b1_0_1 ← Array.index_usize a1_0_1 0#usize
  let c1_0_1 ← lift (core.convert.num.FromU64U32.from b1_0_1)
  let sum1_0_1 ← lift (U64.wrapping_add c1_0_0 c1_0_1)
  let q1_2 ← Array.index_usize state 9#usize
  let a1_0_2 ← reference_poseidon.extension_limbs q1_2
  let b1_0_2 ← Array.index_usize a1_0_2 0#usize
  let c1_0_2 ← lift (core.convert.num.FromU64U32.from b1_0_2)
  let sum1_0_2 ← lift (U64.wrapping_add sum1_0_1 c1_0_2)
  let q1_3 ← Array.index_usize state 13#usize
  let a1_0_3 ← reference_poseidon.extension_limbs q1_3
  let b1_0_3 ← Array.index_usize a1_0_3 0#usize
  let c1_0_3 ← lift (core.convert.num.FromU64U32.from b1_0_3)
  let sum1_0_3 ← lift (U64.wrapping_add sum1_0_2 c1_0_3)
  let a1_1_0 ← reference_poseidon.extension_limbs q1_0
  let b1_1_0 ← Array.index_usize a1_1_0 1#usize
  let c1_1_0 ← lift (core.convert.num.FromU64U32.from b1_1_0)
  let a1_1_1 ← reference_poseidon.extension_limbs q1_1
  let b1_1_1 ← Array.index_usize a1_1_1 1#usize
  let c1_1_1 ← lift (core.convert.num.FromU64U32.from b1_1_1)
  let sum1_1_1 ← lift (U64.wrapping_add c1_1_0 c1_1_1)
  let a1_1_2 ← reference_poseidon.extension_limbs q1_2
  let b1_1_2 ← Array.index_usize a1_1_2 1#usize
  let c1_1_2 ← lift (core.convert.num.FromU64U32.from b1_1_2)
  let sum1_1_2 ← lift (U64.wrapping_add sum1_1_1 c1_1_2)
  let a1_1_3 ← reference_poseidon.extension_limbs q1_3
  let b1_1_3 ← Array.index_usize a1_1_3 1#usize
  let c1_1_3 ← lift (core.convert.num.FromU64U32.from b1_1_3)
  let sum1_1_3 ← lift (U64.wrapping_add sum1_1_2 c1_1_3)
  let a1_2_0 ← reference_poseidon.extension_limbs q1_0
  let b1_2_0 ← Array.index_usize a1_2_0 2#usize
  let c1_2_0 ← lift (core.convert.num.FromU64U32.from b1_2_0)
  let a1_2_1 ← reference_poseidon.extension_limbs q1_1
  let b1_2_1 ← Array.index_usize a1_2_1 2#usize
  let c1_2_1 ← lift (core.convert.num.FromU64U32.from b1_2_1)
  let sum1_2_1 ← lift (U64.wrapping_add c1_2_0 c1_2_1)
  let a1_2_2 ← reference_poseidon.extension_limbs q1_2
  let b1_2_2 ← Array.index_usize a1_2_2 2#usize
  let c1_2_2 ← lift (core.convert.num.FromU64U32.from b1_2_2)
  let sum1_2_2 ← lift (U64.wrapping_add sum1_2_1 c1_2_2)
  let a1_2_3 ← reference_poseidon.extension_limbs q1_3
  let b1_2_3 ← Array.index_usize a1_2_3 2#usize
  let c1_2_3 ← lift (core.convert.num.FromU64U32.from b1_2_3)
  let sum1_2_3 ← lift (U64.wrapping_add sum1_2_2 c1_2_3)
  let a1_3_0 ← reference_poseidon.extension_limbs q1_0
  let b1_3_0 ← Array.index_usize a1_3_0 3#usize
  let c1_3_0 ← lift (core.convert.num.FromU64U32.from b1_3_0)
  let a1_3_1 ← reference_poseidon.extension_limbs q1_1
  let b1_3_1 ← Array.index_usize a1_3_1 3#usize
  let c1_3_1 ← lift (core.convert.num.FromU64U32.from b1_3_1)
  let sum1_3_1 ← lift (U64.wrapping_add c1_3_0 c1_3_1)
  let a1_3_2 ← reference_poseidon.extension_limbs q1_2
  let b1_3_2 ← Array.index_usize a1_3_2 3#usize
  let c1_3_2 ← lift (core.convert.num.FromU64U32.from b1_3_2)
  let sum1_3_2 ← lift (U64.wrapping_add sum1_3_1 c1_3_2)
  let a1_3_3 ← reference_poseidon.extension_limbs q1_3
  let b1_3_3 ← Array.index_usize a1_3_3 3#usize
  let c1_3_3 ← lift (core.convert.num.FromU64U32.from b1_3_3)
  let sum1_3_3 ← lift (U64.wrapping_add sum1_3_2 c1_3_3)
  let q2_0 ← Array.index_usize state 2#usize
  let a2_0_0 ← reference_poseidon.extension_limbs q2_0
  let b2_0_0 ← Array.index_usize a2_0_0 0#usize
  let c2_0_0 ← lift (core.convert.num.FromU64U32.from b2_0_0)
  let q2_1 ← Array.index_usize state 6#usize
  let a2_0_1 ← reference_poseidon.extension_limbs q2_1
  let b2_0_1 ← Array.index_usize a2_0_1 0#usize
  let c2_0_1 ← lift (core.convert.num.FromU64U32.from b2_0_1)
  let sum2_0_1 ← lift (U64.wrapping_add c2_0_0 c2_0_1)
  let q2_2 ← Array.index_usize state 10#usize
  let a2_0_2 ← reference_poseidon.extension_limbs q2_2
  let b2_0_2 ← Array.index_usize a2_0_2 0#usize
  let c2_0_2 ← lift (core.convert.num.FromU64U32.from b2_0_2)
  let sum2_0_2 ← lift (U64.wrapping_add sum2_0_1 c2_0_2)
  let q2_3 ← Array.index_usize state 14#usize
  let a2_0_3 ← reference_poseidon.extension_limbs q2_3
  let b2_0_3 ← Array.index_usize a2_0_3 0#usize
  let c2_0_3 ← lift (core.convert.num.FromU64U32.from b2_0_3)
  let sum2_0_3 ← lift (U64.wrapping_add sum2_0_2 c2_0_3)
  let a2_1_0 ← reference_poseidon.extension_limbs q2_0
  let b2_1_0 ← Array.index_usize a2_1_0 1#usize
  let c2_1_0 ← lift (core.convert.num.FromU64U32.from b2_1_0)
  let a2_1_1 ← reference_poseidon.extension_limbs q2_1
  let b2_1_1 ← Array.index_usize a2_1_1 1#usize
  let c2_1_1 ← lift (core.convert.num.FromU64U32.from b2_1_1)
  let sum2_1_1 ← lift (U64.wrapping_add c2_1_0 c2_1_1)
  let a2_1_2 ← reference_poseidon.extension_limbs q2_2
  let b2_1_2 ← Array.index_usize a2_1_2 1#usize
  let c2_1_2 ← lift (core.convert.num.FromU64U32.from b2_1_2)
  let sum2_1_2 ← lift (U64.wrapping_add sum2_1_1 c2_1_2)
  let a2_1_3 ← reference_poseidon.extension_limbs q2_3
  let b2_1_3 ← Array.index_usize a2_1_3 1#usize
  let c2_1_3 ← lift (core.convert.num.FromU64U32.from b2_1_3)
  let sum2_1_3 ← lift (U64.wrapping_add sum2_1_2 c2_1_3)
  let a2_2_0 ← reference_poseidon.extension_limbs q2_0
  let b2_2_0 ← Array.index_usize a2_2_0 2#usize
  let c2_2_0 ← lift (core.convert.num.FromU64U32.from b2_2_0)
  let a2_2_1 ← reference_poseidon.extension_limbs q2_1
  let b2_2_1 ← Array.index_usize a2_2_1 2#usize
  let c2_2_1 ← lift (core.convert.num.FromU64U32.from b2_2_1)
  let sum2_2_1 ← lift (U64.wrapping_add c2_2_0 c2_2_1)
  let a2_2_2 ← reference_poseidon.extension_limbs q2_2
  let b2_2_2 ← Array.index_usize a2_2_2 2#usize
  let c2_2_2 ← lift (core.convert.num.FromU64U32.from b2_2_2)
  let sum2_2_2 ← lift (U64.wrapping_add sum2_2_1 c2_2_2)
  let a2_2_3 ← reference_poseidon.extension_limbs q2_3
  let b2_2_3 ← Array.index_usize a2_2_3 2#usize
  let c2_2_3 ← lift (core.convert.num.FromU64U32.from b2_2_3)
  let sum2_2_3 ← lift (U64.wrapping_add sum2_2_2 c2_2_3)
  let a2_3_0 ← reference_poseidon.extension_limbs q2_0
  let b2_3_0 ← Array.index_usize a2_3_0 3#usize
  let c2_3_0 ← lift (core.convert.num.FromU64U32.from b2_3_0)
  let a2_3_1 ← reference_poseidon.extension_limbs q2_1
  let b2_3_1 ← Array.index_usize a2_3_1 3#usize
  let c2_3_1 ← lift (core.convert.num.FromU64U32.from b2_3_1)
  let sum2_3_1 ← lift (U64.wrapping_add c2_3_0 c2_3_1)
  let a2_3_2 ← reference_poseidon.extension_limbs q2_2
  let b2_3_2 ← Array.index_usize a2_3_2 3#usize
  let c2_3_2 ← lift (core.convert.num.FromU64U32.from b2_3_2)
  let sum2_3_2 ← lift (U64.wrapping_add sum2_3_1 c2_3_2)
  let a2_3_3 ← reference_poseidon.extension_limbs q2_3
  let b2_3_3 ← Array.index_usize a2_3_3 3#usize
  let c2_3_3 ← lift (core.convert.num.FromU64U32.from b2_3_3)
  let sum2_3_3 ← lift (U64.wrapping_add sum2_3_2 c2_3_3)
  let q3_0 ← Array.index_usize state 3#usize
  let a3_0_0 ← reference_poseidon.extension_limbs q3_0
  let b3_0_0 ← Array.index_usize a3_0_0 0#usize
  let c3_0_0 ← lift (core.convert.num.FromU64U32.from b3_0_0)
  let q3_1 ← Array.index_usize state 7#usize
  let a3_0_1 ← reference_poseidon.extension_limbs q3_1
  let b3_0_1 ← Array.index_usize a3_0_1 0#usize
  let c3_0_1 ← lift (core.convert.num.FromU64U32.from b3_0_1)
  let sum3_0_1 ← lift (U64.wrapping_add c3_0_0 c3_0_1)
  let q3_2 ← Array.index_usize state 11#usize
  let a3_0_2 ← reference_poseidon.extension_limbs q3_2
  let b3_0_2 ← Array.index_usize a3_0_2 0#usize
  let c3_0_2 ← lift (core.convert.num.FromU64U32.from b3_0_2)
  let sum3_0_2 ← lift (U64.wrapping_add sum3_0_1 c3_0_2)
  let q3_3 ← Array.index_usize state 15#usize
  let a3_0_3 ← reference_poseidon.extension_limbs q3_3
  let b3_0_3 ← Array.index_usize a3_0_3 0#usize
  let c3_0_3 ← lift (core.convert.num.FromU64U32.from b3_0_3)
  let sum3_0_3 ← lift (U64.wrapping_add sum3_0_2 c3_0_3)
  let a3_1_0 ← reference_poseidon.extension_limbs q3_0
  let b3_1_0 ← Array.index_usize a3_1_0 1#usize
  let c3_1_0 ← lift (core.convert.num.FromU64U32.from b3_1_0)
  let a3_1_1 ← reference_poseidon.extension_limbs q3_1
  let b3_1_1 ← Array.index_usize a3_1_1 1#usize
  let c3_1_1 ← lift (core.convert.num.FromU64U32.from b3_1_1)
  let sum3_1_1 ← lift (U64.wrapping_add c3_1_0 c3_1_1)
  let a3_1_2 ← reference_poseidon.extension_limbs q3_2
  let b3_1_2 ← Array.index_usize a3_1_2 1#usize
  let c3_1_2 ← lift (core.convert.num.FromU64U32.from b3_1_2)
  let sum3_1_2 ← lift (U64.wrapping_add sum3_1_1 c3_1_2)
  let a3_1_3 ← reference_poseidon.extension_limbs q3_3
  let b3_1_3 ← Array.index_usize a3_1_3 1#usize
  let c3_1_3 ← lift (core.convert.num.FromU64U32.from b3_1_3)
  let sum3_1_3 ← lift (U64.wrapping_add sum3_1_2 c3_1_3)
  let a3_2_0 ← reference_poseidon.extension_limbs q3_0
  let b3_2_0 ← Array.index_usize a3_2_0 2#usize
  let c3_2_0 ← lift (core.convert.num.FromU64U32.from b3_2_0)
  let a3_2_1 ← reference_poseidon.extension_limbs q3_1
  let b3_2_1 ← Array.index_usize a3_2_1 2#usize
  let c3_2_1 ← lift (core.convert.num.FromU64U32.from b3_2_1)
  let sum3_2_1 ← lift (U64.wrapping_add c3_2_0 c3_2_1)
  let a3_2_2 ← reference_poseidon.extension_limbs q3_2
  let b3_2_2 ← Array.index_usize a3_2_2 2#usize
  let c3_2_2 ← lift (core.convert.num.FromU64U32.from b3_2_2)
  let sum3_2_2 ← lift (U64.wrapping_add sum3_2_1 c3_2_2)
  let a3_2_3 ← reference_poseidon.extension_limbs q3_3
  let b3_2_3 ← Array.index_usize a3_2_3 2#usize
  let c3_2_3 ← lift (core.convert.num.FromU64U32.from b3_2_3)
  let sum3_2_3 ← lift (U64.wrapping_add sum3_2_2 c3_2_3)
  let a3_3_0 ← reference_poseidon.extension_limbs q3_0
  let b3_3_0 ← Array.index_usize a3_3_0 3#usize
  let c3_3_0 ← lift (core.convert.num.FromU64U32.from b3_3_0)
  let a3_3_1 ← reference_poseidon.extension_limbs q3_1
  let b3_3_1 ← Array.index_usize a3_3_1 3#usize
  let c3_3_1 ← lift (core.convert.num.FromU64U32.from b3_3_1)
  let sum3_3_1 ← lift (U64.wrapping_add c3_3_0 c3_3_1)
  let a3_3_2 ← reference_poseidon.extension_limbs q3_2
  let b3_3_2 ← Array.index_usize a3_3_2 3#usize
  let c3_3_2 ← lift (core.convert.num.FromU64U32.from b3_3_2)
  let sum3_3_2 ← lift (U64.wrapping_add sum3_3_1 c3_3_2)
  let a3_3_3 ← reference_poseidon.extension_limbs q3_3
  let b3_3_3 ← Array.index_usize a3_3_3 3#usize
  let c3_3_3 ← lift (core.convert.num.FromU64U32.from b3_3_3)
  let sum3_3_3 ← lift (U64.wrapping_add sum3_3_2 c3_3_3)
  .ok (Array.make 4#usize [
    Array.make 4#usize [sum0_0_3,sum0_1_3,sum0_2_3,sum0_3_3] (by simp only [List.length_cons,List.length_nil]; rfl),
    Array.make 4#usize [sum1_0_3,sum1_1_3,sum1_2_3,sum1_3_3] (by simp only [List.length_cons,List.length_nil]; rfl),
    Array.make 4#usize [sum2_0_3,sum2_1_3,sum2_2_3,sum2_3_3] (by simp only [List.length_cons,List.length_nil]; rfl),
    Array.make 4#usize [sum3_0_3,sum3_1_3,sum3_2_3,sum3_3_3] (by simp only [List.length_cons,List.length_nil]; rfl)
  ] (by simp only [List.length_cons,List.length_nil]; rfl))

attribute [local irreducible] Aeneas.Std.bind Array.index_usize
  reference_poseidon.extension_limbs U64.wrapping_add core.convert.num.FromU64U32.from

theorem external_sums_reference554 (state : Array aspis_core.field.QM31 16#usize) :
    external_sums_source554 state = reference_poseidon.global_sums227 state := by
  unfold external_sums_source554 reference_poseidon.global_sums227
  as_aux_lemma =>
    apply bind_equal9
    intro q
    apply bind_equal9
    intro a
    apply bind_equal9
    intro i
    apply bind_equal9
    intro i1
    apply bind_equal9
    intro q1
    apply bind_equal9
    intro a1
    apply bind_equal9
    intro i2
    apply bind_equal9
    intro i3
    apply bind_equal9
    intro i4
    apply bind_equal9
    intro q2
    apply bind_equal9
    intro a2
    apply bind_equal9
    intro i5
    apply bind_equal9
    intro i6
    apply bind_equal9
    intro i7
    apply bind_equal9
    intro q3
    apply bind_equal9
    intro a3
    as_aux_lemma =>
      apply bind_equal9
      intro i8
      apply bind_equal9
      intro i9
      apply bind_equal9
      intro i10
      apply bind_equal9
      intro a4
      apply bind_equal9
      intro i11
      apply bind_equal9
      intro i12
      apply bind_equal9
      intro a5
      apply bind_equal9
      intro i13
      apply bind_equal9
      intro i14
      apply bind_equal9
      intro i15
      apply bind_equal9
      intro a6
      apply bind_equal9
      intro i16
      apply bind_equal9
      intro i17
      apply bind_equal9
      intro i18
      apply bind_equal9
      intro a7
      apply bind_equal9
      intro i19
      as_aux_lemma =>
        apply bind_equal9
        intro i20
        apply bind_equal9
        intro i21
        apply bind_equal9
        intro a8
        apply bind_equal9
        intro i22
        apply bind_equal9
        intro i23
        apply bind_equal9
        intro a9
        apply bind_equal9
        intro i24
        apply bind_equal9
        intro i25
        apply bind_equal9
        intro i26
        apply bind_equal9
        intro a10
        apply bind_equal9
        intro i27
        apply bind_equal9
        intro i28
        apply bind_equal9
        intro i29
        apply bind_equal9
        intro a11
        apply bind_equal9
        intro i30
        apply bind_equal9
        intro i31
        as_aux_lemma =>
          apply bind_equal9
          intro i32
          apply bind_equal9
          intro a12
          apply bind_equal9
          intro i33
          apply bind_equal9
          intro i34
          apply bind_equal9
          intro a13
          apply bind_equal9
          intro i35
          apply bind_equal9
          intro i36
          apply bind_equal9
          intro i37
          apply bind_equal9
          intro a14
          apply bind_equal9
          intro i38
          apply bind_equal9
          intro i39
          apply bind_equal9
          intro i40
          apply bind_equal9
          intro a15
          apply bind_equal9
          intro i41
          apply bind_equal9
          intro i42
          apply bind_equal9
          intro i43
          as_aux_lemma =>
            apply bind_equal9
            intro q4
            apply bind_equal9
            intro a16
            apply bind_equal9
            intro i44
            apply bind_equal9
            intro i45
            apply bind_equal9
            intro q5
            apply bind_equal9
            intro a17
            apply bind_equal9
            intro i46
            apply bind_equal9
            intro i47
            apply bind_equal9
            intro i48
            apply bind_equal9
            intro q6
            apply bind_equal9
            intro a18
            apply bind_equal9
            intro i49
            apply bind_equal9
            intro i50
            apply bind_equal9
            intro i51
            apply bind_equal9
            intro q7
            apply bind_equal9
            intro a19
            as_aux_lemma =>
              apply bind_equal9
              intro i52
              apply bind_equal9
              intro i53
              apply bind_equal9
              intro i54
              apply bind_equal9
              intro a20
              apply bind_equal9
              intro i55
              apply bind_equal9
              intro i56
              apply bind_equal9
              intro a21
              apply bind_equal9
              intro i57
              apply bind_equal9
              intro i58
              apply bind_equal9
              intro i59
              apply bind_equal9
              intro a22
              apply bind_equal9
              intro i60
              apply bind_equal9
              intro i61
              apply bind_equal9
              intro i62
              apply bind_equal9
              intro a23
              apply bind_equal9
              intro i63
              as_aux_lemma =>
                apply bind_equal9
                intro i64
                apply bind_equal9
                intro i65
                apply bind_equal9
                intro a24
                apply bind_equal9
                intro i66
                apply bind_equal9
                intro i67
                apply bind_equal9
                intro a25
                apply bind_equal9
                intro i68
                apply bind_equal9
                intro i69
                apply bind_equal9
                intro i70
                apply bind_equal9
                intro a26
                apply bind_equal9
                intro i71
                apply bind_equal9
                intro i72
                apply bind_equal9
                intro i73
                apply bind_equal9
                intro a27
                apply bind_equal9
                intro i74
                apply bind_equal9
                intro i75
                as_aux_lemma =>
                  apply bind_equal9
                  intro i76
                  apply bind_equal9
                  intro a28
                  apply bind_equal9
                  intro i77
                  apply bind_equal9
                  intro i78
                  apply bind_equal9
                  intro a29
                  apply bind_equal9
                  intro i79
                  apply bind_equal9
                  intro i80
                  apply bind_equal9
                  intro i81
                  apply bind_equal9
                  intro a30
                  apply bind_equal9
                  intro i82
                  apply bind_equal9
                  intro i83
                  apply bind_equal9
                  intro i84
                  apply bind_equal9
                  intro a31
                  apply bind_equal9
                  intro i85
                  apply bind_equal9
                  intro i86
                  apply bind_equal9
                  intro i87
                  as_aux_lemma =>
                    apply bind_equal9
                    intro q8
                    apply bind_equal9
                    intro a32
                    apply bind_equal9
                    intro i88
                    apply bind_equal9
                    intro i89
                    apply bind_equal9
                    intro q9
                    apply bind_equal9
                    intro a33
                    apply bind_equal9
                    intro i90
                    apply bind_equal9
                    intro i91
                    apply bind_equal9
                    intro i92
                    apply bind_equal9
                    intro q10
                    apply bind_equal9
                    intro a34
                    apply bind_equal9
                    intro i93
                    apply bind_equal9
                    intro i94
                    apply bind_equal9
                    intro i95
                    apply bind_equal9
                    intro q11
                    apply bind_equal9
                    intro a35
                    as_aux_lemma =>
                      apply bind_equal9
                      intro i96
                      apply bind_equal9
                      intro i97
                      apply bind_equal9
                      intro i98
                      apply bind_equal9
                      intro a36
                      apply bind_equal9
                      intro i99
                      apply bind_equal9
                      intro i100
                      apply bind_equal9
                      intro a37
                      apply bind_equal9
                      intro i101
                      apply bind_equal9
                      intro i102
                      apply bind_equal9
                      intro i103
                      apply bind_equal9
                      intro a38
                      apply bind_equal9
                      intro i104
                      apply bind_equal9
                      intro i105
                      apply bind_equal9
                      intro i106
                      apply bind_equal9
                      intro a39
                      apply bind_equal9
                      intro i107
                      as_aux_lemma =>
                        apply bind_equal9
                        intro i108
                        apply bind_equal9
                        intro i109
                        apply bind_equal9
                        intro a40
                        apply bind_equal9
                        intro i110
                        apply bind_equal9
                        intro i111
                        apply bind_equal9
                        intro a41
                        apply bind_equal9
                        intro i112
                        apply bind_equal9
                        intro i113
                        apply bind_equal9
                        intro i114
                        apply bind_equal9
                        intro a42
                        apply bind_equal9
                        intro i115
                        apply bind_equal9
                        intro i116
                        apply bind_equal9
                        intro i117
                        apply bind_equal9
                        intro a43
                        apply bind_equal9
                        intro i118
                        apply bind_equal9
                        intro i119
                        as_aux_lemma =>
                          apply bind_equal9
                          intro i120
                          apply bind_equal9
                          intro a44
                          apply bind_equal9
                          intro i121
                          apply bind_equal9
                          intro i122
                          apply bind_equal9
                          intro a45
                          apply bind_equal9
                          intro i123
                          apply bind_equal9
                          intro i124
                          apply bind_equal9
                          intro i125
                          apply bind_equal9
                          intro a46
                          apply bind_equal9
                          intro i126
                          apply bind_equal9
                          intro i127
                          apply bind_equal9
                          intro i128
                          apply bind_equal9
                          intro a47
                          apply bind_equal9
                          intro i129
                          apply bind_equal9
                          intro i130
                          apply bind_equal9
                          intro i131
                          as_aux_lemma =>
                            apply bind_equal9
                            intro q12
                            apply bind_equal9
                            intro a48
                            apply bind_equal9
                            intro i132
                            apply bind_equal9
                            intro i133
                            apply bind_equal9
                            intro q13
                            apply bind_equal9
                            intro a49
                            apply bind_equal9
                            intro i134
                            apply bind_equal9
                            intro i135
                            apply bind_equal9
                            intro i136
                            apply bind_equal9
                            intro q14
                            apply bind_equal9
                            intro a50
                            apply bind_equal9
                            intro i137
                            apply bind_equal9
                            intro i138
                            apply bind_equal9
                            intro i139
                            apply bind_equal9
                            intro q15
                            apply bind_equal9
                            intro a51
                            as_aux_lemma =>
                              apply bind_equal9
                              intro i140
                              apply bind_equal9
                              intro i141
                              apply bind_equal9
                              intro i142
                              apply bind_equal9
                              intro a52
                              apply bind_equal9
                              intro i143
                              apply bind_equal9
                              intro i144
                              apply bind_equal9
                              intro a53
                              apply bind_equal9
                              intro i145
                              apply bind_equal9
                              intro i146
                              apply bind_equal9
                              intro i147
                              apply bind_equal9
                              intro a54
                              apply bind_equal9
                              intro i148
                              apply bind_equal9
                              intro i149
                              apply bind_equal9
                              intro i150
                              apply bind_equal9
                              intro a55
                              apply bind_equal9
                              intro i151
                              as_aux_lemma =>
                                apply bind_equal9
                                intro i152
                                apply bind_equal9
                                intro i153
                                apply bind_equal9
                                intro a56
                                apply bind_equal9
                                intro i154
                                apply bind_equal9
                                intro i155
                                apply bind_equal9
                                intro a57
                                apply bind_equal9
                                intro i156
                                apply bind_equal9
                                intro i157
                                apply bind_equal9
                                intro i158
                                apply bind_equal9
                                intro a58
                                apply bind_equal9
                                intro i159
                                apply bind_equal9
                                intro i160
                                apply bind_equal9
                                intro i161
                                apply bind_equal9
                                intro a59
                                apply bind_equal9
                                intro i162
                                apply bind_equal9
                                intro i163
                                as_aux_lemma =>
                                  apply bind_equal9
                                  intro i164
                                  apply bind_equal9
                                  intro a60
                                  apply bind_equal9
                                  intro i165
                                  apply bind_equal9
                                  intro i166
                                  apply bind_equal9
                                  intro a61
                                  apply bind_equal9
                                  intro i167
                                  apply bind_equal9
                                  intro i168
                                  apply bind_equal9
                                  intro i169
                                  apply bind_equal9
                                  intro a62
                                  apply bind_equal9
                                  intro i170
                                  apply bind_equal9
                                  intro i171
                                  apply bind_equal9
                                  intro i172
                                  apply bind_equal9
                                  intro a63
                                  apply bind_equal9
                                  intro i173
                                  apply bind_equal9
                                  intro i174
                                  apply bind_equal9
                                  intro i175
                                  rfl

#print axioms external_sums_reference554
end PV_B3P_Association554227
