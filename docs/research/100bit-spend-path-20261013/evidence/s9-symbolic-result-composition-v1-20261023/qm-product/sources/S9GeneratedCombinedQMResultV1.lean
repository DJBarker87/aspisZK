import S9QMSquareMixedProductMapV1
import S9QMSquareByRMapV1
import S9SourceResultTransportV1
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace AspisR1S9GeneratedCombinedQMResultV1
abbrev SourceCM := AspisR1S9SquareMulQMCutV1.field.CM31
abbrev TargetCM := AspisR1S9ActualQMMulCutV1.field.CM31
abbrev SourceQM := AspisR1S9SquareMulQMCutV1.field.QM31
abbrev TargetQM := AspisR1S9ActualQMMulCutV1.field.QM31
abbrev mapCM : SourceCM → TargetCM := AspisR1S9QMSquareMixedProductMapV1.mapActualCM
def mapQM (q : SourceQM) : TargetQM := ⟨mapCM q.c0,mapCM q.c1⟩
abbrev mapResult {A B : Type} (f : A → B) (r : Result A) : Result B :=
  AspisR1S9SourceResultTransportV1.mapResult f r

/-- Exact source call order. Scoped source and target names are distinct.
Every component map preserves failure and divergence; no success is assumed. -/
theorem combined_qm_mul_maps (x y : SourceQM) :
    mapResult mapQM (AspisR1S9SquareMulQMCutV1.field.QM31.mul x y) =
      AspisR1S9ActualQMMulCutV1.field.QM31.mul (mapQM x) (mapQM y) := by
  unfold AspisR1S9SquareMulQMCutV1.field.QM31.mul AspisR1S9ActualQMMulCutV1.field.QM31.mul
  change mapResult mapQM (do
      let s0 ← AspisR1S9SquareMulQMCutV1.field.CM31.mul x.c0 y.c0
      let s1 ← AspisR1S9SquareMulQMCutV1.field.CM31.mul x.c1 y.c1
      let s2 ← AspisR1S9SquareMulQMCutV1.field.CM31.add x.c0 x.c1
      let s3 ← AspisR1S9SquareMulQMCutV1.field.CM31.add y.c0 y.c1
      let s4 ← AspisR1S9SquareMulQMCutV1.field.CM31.mul s2 s3
      let s5 ← AspisR1S9SquareMulQMCutV1.field.mul_by_r s1
      let s6 ← AspisR1S9SquareMulQMCutV1.field.CM31.add s0 s5
      let s7 ← AspisR1S9SquareMulQMCutV1.field.CM31.sub s4 s0
      let s8 ← AspisR1S9SquareMulQMCutV1.field.CM31.sub s7 s1
      ok ({ c0 := s6, c1 := s8 } : SourceQM) ) = (do
      let t0 ← AspisR1S9ActualQMMulCutV1.field.CM31.mul (mapCM x.c0) (mapCM y.c0)
      let t1 ← AspisR1S9ActualQMMulCutV1.field.CM31.mul (mapCM x.c1) (mapCM y.c1)
      let t2 ← AspisR1S9ActualQMMulCutV1.field.CM31.add (mapCM x.c0) (mapCM x.c1)
      let t3 ← AspisR1S9ActualQMMulCutV1.field.CM31.add (mapCM y.c0) (mapCM y.c1)
      let t4 ← AspisR1S9ActualQMMulCutV1.field.CM31.mul t2 t3
      let t5 ← AspisR1S9ActualQMMulCutV1.field.mul_by_r t1
      let t6 ← AspisR1S9ActualQMMulCutV1.field.CM31.add t0 t5
      let t7 ← AspisR1S9ActualQMMulCutV1.field.CM31.sub t4 t0
      let t8 ← AspisR1S9ActualQMMulCutV1.field.CM31.sub t7 t1
      ok ({ c0 := t6, c1 := t8 } : TargetQM) )
  apply AspisR1S9SourceResultTransportV1.mapResult_bind_eq mapCM mapQM
    (AspisR1S9SquareMulQMCutV1.field.CM31.mul x.c0 y.c0)
    (AspisR1S9ActualQMMulCutV1.field.CM31.mul (mapCM x.c0) (mapCM y.c0))
    (fun s0 => do
      let s1 ← AspisR1S9SquareMulQMCutV1.field.CM31.mul x.c1 y.c1
      let s2 ← AspisR1S9SquareMulQMCutV1.field.CM31.add x.c0 x.c1
      let s3 ← AspisR1S9SquareMulQMCutV1.field.CM31.add y.c0 y.c1
      let s4 ← AspisR1S9SquareMulQMCutV1.field.CM31.mul s2 s3
      let s5 ← AspisR1S9SquareMulQMCutV1.field.mul_by_r s1
      let s6 ← AspisR1S9SquareMulQMCutV1.field.CM31.add s0 s5
      let s7 ← AspisR1S9SquareMulQMCutV1.field.CM31.sub s4 s0
      let s8 ← AspisR1S9SquareMulQMCutV1.field.CM31.sub s7 s1
      ok ({ c0 := s6, c1 := s8 } : SourceQM))
    (fun t0 => do
      let t1 ← AspisR1S9ActualQMMulCutV1.field.CM31.mul (mapCM x.c1) (mapCM y.c1)
      let t2 ← AspisR1S9ActualQMMulCutV1.field.CM31.add (mapCM x.c0) (mapCM x.c1)
      let t3 ← AspisR1S9ActualQMMulCutV1.field.CM31.add (mapCM y.c0) (mapCM y.c1)
      let t4 ← AspisR1S9ActualQMMulCutV1.field.CM31.mul t2 t3
      let t5 ← AspisR1S9ActualQMMulCutV1.field.mul_by_r t1
      let t6 ← AspisR1S9ActualQMMulCutV1.field.CM31.add t0 t5
      let t7 ← AspisR1S9ActualQMMulCutV1.field.CM31.sub t4 t0
      let t8 ← AspisR1S9ActualQMMulCutV1.field.CM31.sub t7 t1
      ok ({ c0 := t6, c1 := t8 } : TargetQM))
    (AspisR1S9QMSquareMixedProductMapV1.cm_mul_map x.c0 y.c0)
  intro s0
  apply AspisR1S9SourceResultTransportV1.mapResult_bind_eq mapCM mapQM
    (AspisR1S9SquareMulQMCutV1.field.CM31.mul x.c1 y.c1)
    (AspisR1S9ActualQMMulCutV1.field.CM31.mul (mapCM x.c1) (mapCM y.c1))
    (fun s1 => do
      let s2 ← AspisR1S9SquareMulQMCutV1.field.CM31.add x.c0 x.c1
      let s3 ← AspisR1S9SquareMulQMCutV1.field.CM31.add y.c0 y.c1
      let s4 ← AspisR1S9SquareMulQMCutV1.field.CM31.mul s2 s3
      let s5 ← AspisR1S9SquareMulQMCutV1.field.mul_by_r s1
      let s6 ← AspisR1S9SquareMulQMCutV1.field.CM31.add s0 s5
      let s7 ← AspisR1S9SquareMulQMCutV1.field.CM31.sub s4 s0
      let s8 ← AspisR1S9SquareMulQMCutV1.field.CM31.sub s7 s1
      ok ({ c0 := s6, c1 := s8 } : SourceQM))
    (fun t1 => do
      let t2 ← AspisR1S9ActualQMMulCutV1.field.CM31.add (mapCM x.c0) (mapCM x.c1)
      let t3 ← AspisR1S9ActualQMMulCutV1.field.CM31.add (mapCM y.c0) (mapCM y.c1)
      let t4 ← AspisR1S9ActualQMMulCutV1.field.CM31.mul t2 t3
      let t5 ← AspisR1S9ActualQMMulCutV1.field.mul_by_r t1
      let t6 ← AspisR1S9ActualQMMulCutV1.field.CM31.add (mapCM s0) t5
      let t7 ← AspisR1S9ActualQMMulCutV1.field.CM31.sub t4 (mapCM s0)
      let t8 ← AspisR1S9ActualQMMulCutV1.field.CM31.sub t7 t1
      ok ({ c0 := t6, c1 := t8 } : TargetQM))
    (AspisR1S9QMSquareMixedProductMapV1.cm_mul_map x.c1 y.c1)
  intro s1
  apply AspisR1S9SourceResultTransportV1.mapResult_bind_eq mapCM mapQM
    (AspisR1S9SquareMulQMCutV1.field.CM31.add x.c0 x.c1)
    (AspisR1S9ActualQMMulCutV1.field.CM31.add (mapCM x.c0) (mapCM x.c1))
    (fun s2 => do
      let s3 ← AspisR1S9SquareMulQMCutV1.field.CM31.add y.c0 y.c1
      let s4 ← AspisR1S9SquareMulQMCutV1.field.CM31.mul s2 s3
      let s5 ← AspisR1S9SquareMulQMCutV1.field.mul_by_r s1
      let s6 ← AspisR1S9SquareMulQMCutV1.field.CM31.add s0 s5
      let s7 ← AspisR1S9SquareMulQMCutV1.field.CM31.sub s4 s0
      let s8 ← AspisR1S9SquareMulQMCutV1.field.CM31.sub s7 s1
      ok ({ c0 := s6, c1 := s8 } : SourceQM))
    (fun t2 => do
      let t3 ← AspisR1S9ActualQMMulCutV1.field.CM31.add (mapCM y.c0) (mapCM y.c1)
      let t4 ← AspisR1S9ActualQMMulCutV1.field.CM31.mul t2 t3
      let t5 ← AspisR1S9ActualQMMulCutV1.field.mul_by_r (mapCM s1)
      let t6 ← AspisR1S9ActualQMMulCutV1.field.CM31.add (mapCM s0) t5
      let t7 ← AspisR1S9ActualQMMulCutV1.field.CM31.sub t4 (mapCM s0)
      let t8 ← AspisR1S9ActualQMMulCutV1.field.CM31.sub t7 (mapCM s1)
      ok ({ c0 := t6, c1 := t8 } : TargetQM))
    (AspisR1S9QMSquareMixedProductMapV1.cm_add_map x.c0 x.c1)
  intro s2
  apply AspisR1S9SourceResultTransportV1.mapResult_bind_eq mapCM mapQM
    (AspisR1S9SquareMulQMCutV1.field.CM31.add y.c0 y.c1)
    (AspisR1S9ActualQMMulCutV1.field.CM31.add (mapCM y.c0) (mapCM y.c1))
    (fun s3 => do
      let s4 ← AspisR1S9SquareMulQMCutV1.field.CM31.mul s2 s3
      let s5 ← AspisR1S9SquareMulQMCutV1.field.mul_by_r s1
      let s6 ← AspisR1S9SquareMulQMCutV1.field.CM31.add s0 s5
      let s7 ← AspisR1S9SquareMulQMCutV1.field.CM31.sub s4 s0
      let s8 ← AspisR1S9SquareMulQMCutV1.field.CM31.sub s7 s1
      ok ({ c0 := s6, c1 := s8 } : SourceQM))
    (fun t3 => do
      let t4 ← AspisR1S9ActualQMMulCutV1.field.CM31.mul (mapCM s2) t3
      let t5 ← AspisR1S9ActualQMMulCutV1.field.mul_by_r (mapCM s1)
      let t6 ← AspisR1S9ActualQMMulCutV1.field.CM31.add (mapCM s0) t5
      let t7 ← AspisR1S9ActualQMMulCutV1.field.CM31.sub t4 (mapCM s0)
      let t8 ← AspisR1S9ActualQMMulCutV1.field.CM31.sub t7 (mapCM s1)
      ok ({ c0 := t6, c1 := t8 } : TargetQM))
    (AspisR1S9QMSquareMixedProductMapV1.cm_add_map y.c0 y.c1)
  intro s3
  apply AspisR1S9SourceResultTransportV1.mapResult_bind_eq mapCM mapQM
    (AspisR1S9SquareMulQMCutV1.field.CM31.mul s2 s3)
    (AspisR1S9ActualQMMulCutV1.field.CM31.mul (mapCM s2) (mapCM s3))
    (fun s4 => do
      let s5 ← AspisR1S9SquareMulQMCutV1.field.mul_by_r s1
      let s6 ← AspisR1S9SquareMulQMCutV1.field.CM31.add s0 s5
      let s7 ← AspisR1S9SquareMulQMCutV1.field.CM31.sub s4 s0
      let s8 ← AspisR1S9SquareMulQMCutV1.field.CM31.sub s7 s1
      ok ({ c0 := s6, c1 := s8 } : SourceQM))
    (fun t4 => do
      let t5 ← AspisR1S9ActualQMMulCutV1.field.mul_by_r (mapCM s1)
      let t6 ← AspisR1S9ActualQMMulCutV1.field.CM31.add (mapCM s0) t5
      let t7 ← AspisR1S9ActualQMMulCutV1.field.CM31.sub t4 (mapCM s0)
      let t8 ← AspisR1S9ActualQMMulCutV1.field.CM31.sub t7 (mapCM s1)
      ok ({ c0 := t6, c1 := t8 } : TargetQM))
    (AspisR1S9QMSquareMixedProductMapV1.cm_mul_map s2 s3)
  intro s4
  apply AspisR1S9SourceResultTransportV1.mapResult_bind_eq mapCM mapQM
    (AspisR1S9SquareMulQMCutV1.field.mul_by_r s1)
    (AspisR1S9ActualQMMulCutV1.field.mul_by_r (mapCM s1))
    (fun s5 => do
      let s6 ← AspisR1S9SquareMulQMCutV1.field.CM31.add s0 s5
      let s7 ← AspisR1S9SquareMulQMCutV1.field.CM31.sub s4 s0
      let s8 ← AspisR1S9SquareMulQMCutV1.field.CM31.sub s7 s1
      ok ({ c0 := s6, c1 := s8 } : SourceQM))
    (fun t5 => do
      let t6 ← AspisR1S9ActualQMMulCutV1.field.CM31.add (mapCM s0) t5
      let t7 ← AspisR1S9ActualQMMulCutV1.field.CM31.sub (mapCM s4) (mapCM s0)
      let t8 ← AspisR1S9ActualQMMulCutV1.field.CM31.sub t7 (mapCM s1)
      ok ({ c0 := t6, c1 := t8 } : TargetQM))
    (AspisR1S9QMSquareByRMapV1.by_r_maps_to_actual s1)
  intro s5
  apply AspisR1S9SourceResultTransportV1.mapResult_bind_eq mapCM mapQM
    (AspisR1S9SquareMulQMCutV1.field.CM31.add s0 s5)
    (AspisR1S9ActualQMMulCutV1.field.CM31.add (mapCM s0) (mapCM s5))
    (fun s6 => do
      let s7 ← AspisR1S9SquareMulQMCutV1.field.CM31.sub s4 s0
      let s8 ← AspisR1S9SquareMulQMCutV1.field.CM31.sub s7 s1
      ok ({ c0 := s6, c1 := s8 } : SourceQM))
    (fun t6 => do
      let t7 ← AspisR1S9ActualQMMulCutV1.field.CM31.sub (mapCM s4) (mapCM s0)
      let t8 ← AspisR1S9ActualQMMulCutV1.field.CM31.sub t7 (mapCM s1)
      ok ({ c0 := t6, c1 := t8 } : TargetQM))
    (AspisR1S9QMSquareMixedProductMapV1.cm_add_map s0 s5)
  intro s6
  apply AspisR1S9SourceResultTransportV1.mapResult_bind_eq mapCM mapQM
    (AspisR1S9SquareMulQMCutV1.field.CM31.sub s4 s0)
    (AspisR1S9ActualQMMulCutV1.field.CM31.sub (mapCM s4) (mapCM s0))
    (fun s7 => do
      let s8 ← AspisR1S9SquareMulQMCutV1.field.CM31.sub s7 s1
      ok ({ c0 := s6, c1 := s8 } : SourceQM))
    (fun t7 => do
      let t8 ← AspisR1S9ActualQMMulCutV1.field.CM31.sub t7 (mapCM s1)
      ok ({ c0 := (mapCM s6), c1 := t8 } : TargetQM))
    (AspisR1S9QMSquareMixedProductMapV1.cm_sub_map s4 s0)
  intro s7
  apply AspisR1S9SourceResultTransportV1.mapResult_bind_eq mapCM mapQM
    (AspisR1S9SquareMulQMCutV1.field.CM31.sub s7 s1)
    (AspisR1S9ActualQMMulCutV1.field.CM31.sub (mapCM s7) (mapCM s1))
    (fun s8 => do
      ok ({ c0 := s6, c1 := s8 } : SourceQM))
    (fun t8 => do
      ok ({ c0 := (mapCM s6), c1 := t8 } : TargetQM))
    (AspisR1S9QMSquareMixedProductMapV1.cm_sub_map s7 s1)
  intro s8
  rfl
#print axioms combined_qm_mul_maps
end AspisR1S9GeneratedCombinedQMResultV1
