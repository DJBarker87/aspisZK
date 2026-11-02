import PV_B3P_FromFnFour550227
import PV_B3P_P227_02
import PV_B3P_DigestCpsEq9227
namespace PV_B3P_Association554227
open Aeneas Aeneas.Std PV_B3P_227 Result PV_B3P_Binding9227 PV_B3P_Association550227
set_option autoImplicit false

def external_sums_column0_554 {α : Type} (state : Array aspis_core.field.QM31 16#usize) (next : Array U64 4#usize → Result α) : Result α := do
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
  next (Array.make 4#usize [sum0_0_3,sum0_1_3,sum0_2_3,sum0_3_3] (by simp only [List.length_cons,List.length_nil]; rfl))

def external_sums_column1_554 {α : Type} (state : Array aspis_core.field.QM31 16#usize) (next : Array U64 4#usize → Result α) : Result α := do
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
  next (Array.make 4#usize [sum1_0_3,sum1_1_3,sum1_2_3,sum1_3_3] (by simp only [List.length_cons,List.length_nil]; rfl))

def external_sums_column2_554 {α : Type} (state : Array aspis_core.field.QM31 16#usize) (next : Array U64 4#usize → Result α) : Result α := do
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
  next (Array.make 4#usize [sum2_0_3,sum2_1_3,sum2_2_3,sum2_3_3] (by simp only [List.length_cons,List.length_nil]; rfl))

def external_sums_column3_554 {α : Type} (state : Array aspis_core.field.QM31 16#usize) (next : Array U64 4#usize → Result α) : Result α := do
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
  next (Array.make 4#usize [sum3_0_3,sum3_1_3,sum3_2_3,sum3_3_3] (by simp only [List.length_cons,List.length_nil]; rfl))

def external_sums_source554 (state : Array aspis_core.field.QM31 16#usize) : Result (Array (Array U64 4#usize) 4#usize) :=
  external_sums_column0_554 state fun row0 =>
  external_sums_column1_554 state fun row1 =>
  external_sums_column2_554 state fun row2 =>
  external_sums_column3_554 state fun row3 =>
  .ok (Array.make 4#usize [row0,row1,row2,row3] (by simp only [List.length_cons,List.length_nil]; rfl))

#print axioms external_sums_source554
end PV_B3P_Association554227
