import S9CandidateSideOneTailMapV4

set_option autoImplicit false
open Aeneas Aeneas.Std Result

namespace AspisR1S9CandidateTermStagesV1

abbrev C := AspisR1S9CandidateSideOneTailMapV1.C
abbrev P := AspisR1S9CandidateSideOneTailMapV1.P
abbrev CA := AspisR1S9CandidateSideOneTailMapV1.CA
abbrev PA := AspisR1S9CandidateSideOneTailMapV1.PA
abbrev MP (x : C) : P := AspisR1S9CandidateHelperV1.toP6W x
abbrev M1 (x : C × C) : P × P := (MP x.1, MP x.2)
abbrev M2 (x : (C × C) × C) : (P × P) × P := (M1 x.1, MP x.2)
abbrev M3 (x : ((C × C) × C) × C) : ((P × P) × P) × P := (M2 x.1, MP x.2)
abbrev M4 (x : (((C × C) × C) × C) × C) : (((P × P) × P) × P) × P := (M3 x.1, MP x.2)
abbrev M5 (x : ((((C × C) × C) × C) × C) × C) : ((((P × P) × P) × P) × P) × P := (M4 x.1, MP x.2)
def Mout (x : C × C × C) : P × P × P := (MP x.1, MP x.2.1, MP x.2.2)

def c0 (terms : CA) : Result C := Array.index_usize terms 0#usize
def p0 (terms : PA) : Result P := Array.index_usize terms 0#usize

def c1 (terms : CA) (x0 : C) : Result (C × C) := do
  let x1 ← Array.index_usize terms 1#usize
  .ok (x0,x1)
def p1 (terms : PA) (x0 : P) : Result (P × P) := do
  let x1 ← Array.index_usize terms 1#usize
  .ok (x0,x1)

def c2 (x : C × C) : Result ((C × C) × C) := do
  let first2 ← AspisR1S9CandidateHelperV1.field.WideExact.add x.1 x.2
  .ok (x,first2)
def p2 (x : P × P) : Result ((P × P) × P) := do
  let first2 ← @AspisR1S9HelperP6.FieldOps.wideAdd AspisR1S9ConcreteFieldOpsV1.concreteFieldOps x.1 x.2
  .ok (x,first2)

def c3 (terms : CA) (x : (C × C) × C) : Result (((C × C) × C) × C) := do
  let x2 ← Array.index_usize terms 2#usize
  .ok (x,x2)
def p3 (terms : PA) (x : (P × P) × P) : Result (((P × P) × P) × P) := do
  let x2 ← Array.index_usize terms 2#usize
  .ok (x,x2)

def c4 (x : ((C × C) × C) × C) : Result ((((C × C) × C) × C) × C) := do
  let first3 ← AspisR1S9CandidateHelperV1.field.WideExact.add x.1.2 x.2
  .ok (x,first3)
def p4 (x : ((P × P) × P) × P) : Result ((((P × P) × P) × P) × P) := do
  let first3 ← @AspisR1S9HelperP6.FieldOps.wideAdd AspisR1S9ConcreteFieldOpsV1.concreteFieldOps x.1.2 x.2
  .ok (x,first3)

def c5 (terms : CA) (x : (((C × C) × C) × C) × C) : Result (((((C × C) × C) × C) × C) × C) := do
  let x3 ← Array.index_usize terms 3#usize
  .ok (x,x3)
def p5 (terms : PA) (x : (((P × P) × P) × P) × P) : Result (((((P × P) × P) × P) × P) × P) := do
  let x3 ← Array.index_usize terms 3#usize
  .ok (x,x3)

def c6 (x : ((((C × C) × C) × C) × C) × C) : Result (C × C × C) := do
  let all ← AspisR1S9CandidateHelperV1.field.WideExact.add x.1.2 x.2
  .ok (x.1.1.1.2, x.1.2, all)
def p6 (x : ((((P × P) × P) × P) × P) × P) : Result (P × P × P) := do
  let all ← @AspisR1S9HelperP6.FieldOps.wideAdd AspisR1S9ConcreteFieldOpsV1.concreteFieldOps x.1.2 x.2
  .ok (x.1.1.1.2, x.1.2, all)

theorem stage0_maps (terms : CA) :
    AspisR1S9CandidateFoldMapPrimitivesV1.mapResult MP (c0 terms) =
      p0 (AspisR1S9CandidateFoldMapPrimitivesV1.mapArray MP terms) := by
  exact AspisR1S9CandidateFoldMapPrimitivesV1.mapArray_index_result MP terms 0#usize

theorem stage1_maps (terms : CA) (x0 : C) :
    AspisR1S9CandidateFoldMapPrimitivesV1.mapResult M1 (c1 terms x0) =
      p1 (AspisR1S9CandidateFoldMapPrimitivesV1.mapArray MP terms) (MP x0) := by
  unfold c1 p1
  apply AspisR1S9CandidateFoldMapPrimitivesV1.mapResult_bind_congr M1 MP
    (Array.index_usize terms 1#usize)
    (Array.index_usize (AspisR1S9CandidateFoldMapPrimitivesV1.mapArray MP terms) 1#usize)
    (fun x1 => .ok (x0,x1)) (fun x1 => .ok (MP x0,x1))
    (AspisR1S9CandidateFoldMapPrimitivesV1.mapArray_index_result MP terms 1#usize)
    (by intro x1; rfl)

theorem stage2_maps (x : C × C) :
    AspisR1S9CandidateFoldMapPrimitivesV1.mapResult M2 (c2 x) = p2 (M1 x) := by
  unfold c2 p2 M2 M1 MP
  apply AspisR1S9CandidateFoldMapPrimitivesV1.mapResult_bind_congr M2 MP
    (AspisR1S9CandidateHelperV1.field.WideExact.add x.1 x.2)
    (@AspisR1S9HelperP6.FieldOps.wideAdd AspisR1S9ConcreteFieldOpsV1.concreteFieldOps (MP x.1) (MP x.2))
    (fun first2 => .ok (x,first2)) (fun first2 => .ok ((MP x.1,MP x.2),first2))
    (AspisR1S9CandidateHelperBridgeV1.map_wide_add x.1 x.2)
    (by intro first2; rfl)

theorem stage3_maps (terms : CA) (x : (C × C) × C) :
    AspisR1S9CandidateFoldMapPrimitivesV1.mapResult M3 (c3 terms x) =
      p3 (AspisR1S9CandidateFoldMapPrimitivesV1.mapArray MP terms) (M2 x) := by
  unfold c3 p3
  apply AspisR1S9CandidateFoldMapPrimitivesV1.mapResult_bind_congr M3 MP
    (Array.index_usize terms 2#usize)
    (Array.index_usize (AspisR1S9CandidateFoldMapPrimitivesV1.mapArray MP terms) 2#usize)
    (fun x2 => .ok (x,x2)) (fun x2 => .ok (M2 x,x2))
    (AspisR1S9CandidateFoldMapPrimitivesV1.mapArray_index_result MP terms 2#usize)
    (by intro x2; rfl)

theorem stage4_maps (x : ((C × C) × C) × C) :
    AspisR1S9CandidateFoldMapPrimitivesV1.mapResult M4 (c4 x) = p4 (M3 x) := by
  unfold c4 p4 M4 M3
  apply AspisR1S9CandidateFoldMapPrimitivesV1.mapResult_bind_congr M4 MP
    (AspisR1S9CandidateHelperV1.field.WideExact.add x.1.2 x.2)
    (@AspisR1S9HelperP6.FieldOps.wideAdd AspisR1S9ConcreteFieldOpsV1.concreteFieldOps (MP x.1.2) (MP x.2))
    (fun first3 => .ok (x,first3)) (fun first3 => .ok ((M3 x),first3))
    (AspisR1S9CandidateHelperBridgeV1.map_wide_add x.1.2 x.2)
    (by intro first3; rfl)

theorem stage5_maps (terms : CA) (x : (((C × C) × C) × C) × C) :
    AspisR1S9CandidateFoldMapPrimitivesV1.mapResult M5 (c5 terms x) =
      p5 (AspisR1S9CandidateFoldMapPrimitivesV1.mapArray MP terms) (M4 x) := by
  unfold c5 p5
  apply AspisR1S9CandidateFoldMapPrimitivesV1.mapResult_bind_congr M5 MP
    (Array.index_usize terms 3#usize)
    (Array.index_usize (AspisR1S9CandidateFoldMapPrimitivesV1.mapArray MP terms) 3#usize)
    (fun x3 => .ok (x,x3)) (fun x3 => .ok (M4 x,x3))
    (AspisR1S9CandidateFoldMapPrimitivesV1.mapArray_index_result MP terms 3#usize)
    (by intro x3; rfl)

theorem stage6_maps (x : ((((C × C) × C) × C) × C) × C) :
    AspisR1S9CandidateFoldMapPrimitivesV1.mapResult Mout (c6 x) = p6 (M5 x) := by
  unfold c6 p6 Mout M5 M4 M3 M2 M1 MP
  apply AspisR1S9CandidateFoldMapPrimitivesV1.mapResult_bind_congr Mout MP
    (AspisR1S9CandidateHelperV1.field.WideExact.add x.1.2 x.2)
    (@AspisR1S9HelperP6.FieldOps.wideAdd AspisR1S9ConcreteFieldOpsV1.concreteFieldOps (MP x.1.2) (MP x.2))
    (fun all => .ok (x.1.1.1.2,x.1.2,all))
    (fun all => .ok (MP x.1.1.1.2,MP x.1.2,all))
    (AspisR1S9CandidateHelperBridgeV1.map_wide_add x.1.2 x.2)
    (by intro all; rfl)

end AspisR1S9CandidateTermStagesV1

#print axioms AspisR1S9CandidateTermStagesV1.stage0_maps
#print axioms AspisR1S9CandidateTermStagesV1.stage1_maps
#print axioms AspisR1S9CandidateTermStagesV1.stage2_maps
#print axioms AspisR1S9CandidateTermStagesV1.stage3_maps
#print axioms AspisR1S9CandidateTermStagesV1.stage4_maps
#print axioms AspisR1S9CandidateTermStagesV1.stage5_maps
#print axioms AspisR1S9CandidateTermStagesV1.stage6_maps
