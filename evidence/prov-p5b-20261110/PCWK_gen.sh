#!/bin/bash
# generate PRVEq_AspisV8R19_M31mul_k1.lean (PCWK_). lemma blocks copied verbatim from PRVEq_AspisR72Sampler_Funs_A2.lean (P3b/P3x lemmas)
cd "$(dirname "$0")"
A2=../prov-p3x-20261110/PRVEq_AspisR72Sampler_Funs_A2.lean
OUT=PRVEq_AspisV8R19_M31mul_k1.lean
{
cat <<'H'
-- PCWK_ (phase P5b): fresh (frozen 4bb3b3f, overflow ON) = gate for M31.mul in AspisV8R19.{Guarded,Complex,Quartic}FieldSlice,
-- and the gate-only helper r23_product_u32_bounded (QuarticFieldSlice). Lemma blocks PCVB_M31 / PCVB_R23 are verbatim from
-- evidence/prov-p3x-20261110/PRVEq_AspisR72Sampler_Funs_A2.lean (P3b lemmas). All theorems run at the default maxHeartbeats 200000.
import Aeneas
import AspisV8R19.QuarticFieldSlice
open Aeneas Aeneas.Std Result ControlFlow Error
set_option linter.dupNamespace false
set_option linter.hashCommand false
set_option linter.unusedVariables false
set_option maxHeartbeats 200000
set_option maxRecDepth 2048
noncomputable section

H
sed -n 13,180p $A2
echo
sed -n 285,322p $A2
echo
for spec in "R64 Guarded" "R65 Complex" "R66 Quartic"; do
set -- $spec; N=Aspis$1Field; M=$2FieldSlice; F=PRVFresh_AspisV8R19_$M; T=PRVEq.AspisV8R19.$M
cat <<EOT
namespace $N
namespace $F

/-- [aspis_core::field::P]
    Source: 'crates/aspis-core/src/field.rs', lines 19:0-19:31
    Visibility: public -/
@[global_simps, irreducible] def field.P : Std.U32 := 2147483647#u32

/-- [aspis_core::field::reduce_u64]:
    Source: 'crates/aspis-core/src/field.rs', lines 31:0-44:1 -/
def field.reduce_u64 (x : Std.U64) : Result Std.U32 := do
  let i ← lift (UScalar.cast .U64 field.P)
  let i1 ← lift (x &&& i)
  let i2 ← x >>> 31#u32
  let x1 ← i1 + i2
  let i3 ← lift (UScalar.cast .U64 field.P)
  let i4 ← lift (x1 &&& i3)
  let i5 ← x1 >>> 31#u32
  let x2 ← i4 + i5
  let x3 ← lift (UScalar.cast .U32 x2)
  if x3 >= field.P
  then x3 - field.P
  else ok x3

/-- [aspis_core::field::{aspis_core::field::M31}::mul]:
    Source: 'crates/aspis-core/src/field.rs', lines 133:4-137:5
    Visibility: public -/
def field.M31.mul (self : field.M31) (rhs : field.M31) : Result field.M31 := do
  let i ← lift (UScalar.cast .U64 self)
  let i1 ← lift (UScalar.cast .U64 rhs)
  let i2 ← i * i1
  let i3 ← field.reduce_u64 i2
  ok i3

end $F
end $N

set_option maxHeartbeats 200000 in
theorem $T.field.P : @$N.$F.field.P = @$N.field.P := by
  delta $N.$F.field.P $N.field.P; try rfl; done
#print axioms $T.field.P

set_option maxHeartbeats 200000 in
theorem $T.field.reduce_u64 : @$N.$F.field.reduce_u64 = @$N.field.reduce_u64 := by
  delta $N.$F.field.reduce_u64 $N.field.reduce_u64; try simp only [$T.field.P]; try rfl; done
#print axioms $T.field.reduce_u64

-- The gate guard is total on U32 x U32 (the non-fast branches are the frozen reduce_u64 (a*b)); the fast branch is
-- equal to it for a, b < P by PCVB_M31.fast_chain.
set_option maxHeartbeats 200000 in
theorem $T.field.M31.mul : @$N.$F.field.M31.mul = @$N.field.M31.mul := by
  funext self rhs
  have hr : @$N.$F.field.reduce_u64 = @$N.field.reduce_u64 := $T.field.reduce_u64
  have hP : ($N.field.P : Std.U32).val = 2147483647 := by
    unfold $N.field.P; rfl
  unfold $N.$F.field.M31.mul $N.field.M31.mul
  rw [hr]
  by_cases h1 : self < $N.field.P
  · by_cases h2 : rhs < $N.field.P
    · rw [if_pos h1, if_pos h2]
      exact PCVB_M31.fast_chain $N.field.P hP $N.field.reduce_u64 (fun x => rfl) self rhs h1 h2
    · rw [if_pos h1, if_neg h2]
      try rfl
  · rw [if_neg h1]
    try rfl
#print axioms $T.field.M31.mul

EOT
done
cat <<'EOT'
-- P5b: AspisV8R19.QuarticFieldSlice field.r23_product_u32_bounded (source r23_width.rs) has no frozen counterpart at
-- 4bb3b3f; it is a gate-only helper of the gate CM31.mul / CM31.square. Both guards only select an equal-valued u32
-- round trip, so it equals the checked u64 product on ALL inputs (total, no domain).
set_option maxHeartbeats 200000 in
theorem PRVEq.AspisV8R19.QuarticFieldSlice.field.r23_gate : ∀ l r, AspisR66Field.field.r23_product_u32_bounded l r = l * r := fun l r => PCVB_R23.r23_eq l r
#print axioms PRVEq.AspisV8R19.QuarticFieldSlice.field.r23_gate
EOT
} > $OUT
