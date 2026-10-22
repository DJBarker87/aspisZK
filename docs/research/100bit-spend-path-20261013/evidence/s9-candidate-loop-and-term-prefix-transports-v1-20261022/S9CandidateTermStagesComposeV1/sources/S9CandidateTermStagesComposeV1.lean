import S9CandidateTermStagesV1

set_option autoImplicit false
open Aeneas Aeneas.Std Result
open AspisR1S9CandidateTermStagesV1

namespace AspisR1S9CandidateTermStagesComposeV1

abbrev C := AspisR1S9CandidateTermStagesV1.C
abbrev P := AspisR1S9CandidateTermStagesV1.P
abbrev CA := AspisR1S9CandidateTermStagesV1.CA
abbrev PA := AspisR1S9CandidateTermStagesV1.PA
abbrev MP := AspisR1S9CandidateTermStagesV1.MP
abbrev M1 := AspisR1S9CandidateTermStagesV1.M1
abbrev M2 := AspisR1S9CandidateTermStagesV1.M2
abbrev M3 := AspisR1S9CandidateTermStagesV1.M3
abbrev M4 := AspisR1S9CandidateTermStagesV1.M4
abbrev M5 := AspisR1S9CandidateTermStagesV1.M5
abbrev Mout := AspisR1S9CandidateTermStagesV1.Mout

def cSuffix6 (x : ((((C × C) × C) × C) × C) × C) : Result (C × C × C) := c6 x
def pSuffix6 (x : ((((P × P) × P) × P) × P) × P) : Result (P × P × P) := p6 x

def cSuffix5 (terms : CA) (x : (((C × C) × C) × C) × C) : Result (C × C × C) := do
  let x3 ← Array.index_usize terms 3#usize
  cSuffix6 (x,x3)
def pSuffix5 (terms : PA) (x : (((P × P) × P) × P) × P) : Result (P × P × P) := do
  let x3 ← Array.index_usize terms 3#usize
  pSuffix6 (x,x3)

def cSuffix4 (terms : CA) (x : ((C × C) × C) × C) : Result (C × C × C) := do
  let first3 ← AspisR1S9CandidateHelperV1.field.WideExact.add x.1.2 x.2
  cSuffix5 terms (x,first3)
def pSuffix4 (terms : PA) (x : ((P × P) × P) × P) : Result (P × P × P) := do
  let first3 ← @AspisR1S9HelperP6.FieldOps.wideAdd AspisR1S9ConcreteFieldOpsV1.concreteFieldOps x.1.2 x.2
  pSuffix5 terms (x,first3)

def cSuffix3 (terms : CA) (x : (C × C) × C) : Result (C × C × C) := do
  let x2 ← Array.index_usize terms 2#usize
  cSuffix4 terms (x,x2)
def pSuffix3 (terms : PA) (x : (P × P) × P) : Result (P × P × P) := do
  let x2 ← Array.index_usize terms 2#usize
  pSuffix4 terms (x,x2)

def cSuffix2 (terms : CA) (x : C × C) : Result (C × C × C) := do
  let first2 ← AspisR1S9CandidateHelperV1.field.WideExact.add x.1 x.2
  cSuffix3 terms (x,first2)
def pSuffix2 (terms : PA) (x : P × P) : Result (P × P × P) := do
  let first2 ← @AspisR1S9HelperP6.FieldOps.wideAdd AspisR1S9ConcreteFieldOpsV1.concreteFieldOps x.1 x.2
  pSuffix3 terms (x,first2)

def cSuffix1 (terms : CA) (x0 : C) : Result (C × C × C) := do
  let x1 ← Array.index_usize terms 1#usize
  cSuffix2 terms (x0,x1)
def pSuffix1 (terms : PA) (x0 : P) : Result (P × P × P) := do
  let x1 ← Array.index_usize terms 1#usize
  pSuffix2 terms (x0,x1)

def candidateFourTermSums (terms : CA) : Result (C × C × C) := do
  let x0 ← Array.index_usize terms 0#usize
  cSuffix1 terms x0
def p6FourTermSums (terms : PA) : Result (P × P × P) := do
  let x0 ← Array.index_usize terms 0#usize
  pSuffix1 terms x0

theorem suffix6_maps (x : ((((C × C) × C) × C) × C) × C) :
    AspisR1S9CandidateFoldMapPrimitivesV1.mapResult Mout (cSuffix6 x) = pSuffix6 (M5 x) := by
  exact stage6_maps x

theorem suffix5_maps (terms : CA) (x : (((C × C) × C) × C) × C) :
    AspisR1S9CandidateFoldMapPrimitivesV1.mapResult Mout (cSuffix5 terms x) =
      pSuffix5 (AspisR1S9CandidateFoldMapPrimitivesV1.mapArray MP terms) (M4 x) := by
  unfold cSuffix5 pSuffix5
  apply AspisR1S9CandidateFoldMapPrimitivesV1.mapResult_bind_congr Mout MP
    (Array.index_usize terms 3#usize)
    (Array.index_usize (AspisR1S9CandidateFoldMapPrimitivesV1.mapArray MP terms) 3#usize)
    (fun x3 => cSuffix6 (x,x3)) (fun x3 => pSuffix6 (M4 x,x3))
    (AspisR1S9CandidateFoldMapPrimitivesV1.mapArray_index_result MP terms 3#usize)
    (by intro x3; exact suffix6_maps (x,x3))

theorem suffix4_maps (terms : CA) (x : ((C × C) × C) × C) :
    AspisR1S9CandidateFoldMapPrimitivesV1.mapResult Mout (cSuffix4 terms x) =
      pSuffix4 (AspisR1S9CandidateFoldMapPrimitivesV1.mapArray MP terms) (M3 x) := by
  unfold cSuffix4 pSuffix4
  apply AspisR1S9CandidateFoldMapPrimitivesV1.mapResult_bind_congr Mout MP
    (AspisR1S9CandidateHelperV1.field.WideExact.add x.1.2 x.2)
    (@AspisR1S9HelperP6.FieldOps.wideAdd AspisR1S9ConcreteFieldOpsV1.concreteFieldOps (MP x.1.2) (MP x.2))
    (fun first3 => cSuffix5 terms (x,first3))
    (fun first3 => pSuffix5 (AspisR1S9CandidateFoldMapPrimitivesV1.mapArray MP terms) (M3 x,first3))
    (AspisR1S9CandidateHelperBridgeV1.map_wide_add x.1.2 x.2)
    (by intro first3; exact suffix5_maps terms (x,first3))

theorem suffix3_maps (terms : CA) (x : (C × C) × C) :
    AspisR1S9CandidateFoldMapPrimitivesV1.mapResult Mout (cSuffix3 terms x) =
      pSuffix3 (AspisR1S9CandidateFoldMapPrimitivesV1.mapArray MP terms) (M2 x) := by
  unfold cSuffix3 pSuffix3
  apply AspisR1S9CandidateFoldMapPrimitivesV1.mapResult_bind_congr Mout MP
    (Array.index_usize terms 2#usize)
    (Array.index_usize (AspisR1S9CandidateFoldMapPrimitivesV1.mapArray MP terms) 2#usize)
    (fun x2 => cSuffix4 terms (x,x2))
    (fun x2 => pSuffix4 (AspisR1S9CandidateFoldMapPrimitivesV1.mapArray MP terms) (M2 x,x2))
    (AspisR1S9CandidateFoldMapPrimitivesV1.mapArray_index_result MP terms 2#usize)
    (by intro x2; exact suffix4_maps terms (x,x2))

theorem suffix2_maps (terms : CA) (x : C × C) :
    AspisR1S9CandidateFoldMapPrimitivesV1.mapResult Mout (cSuffix2 terms x) =
      pSuffix2 (AspisR1S9CandidateFoldMapPrimitivesV1.mapArray MP terms) (M1 x) := by
  unfold cSuffix2 pSuffix2
  apply AspisR1S9CandidateFoldMapPrimitivesV1.mapResult_bind_congr Mout MP
    (AspisR1S9CandidateHelperV1.field.WideExact.add x.1 x.2)
    (@AspisR1S9HelperP6.FieldOps.wideAdd AspisR1S9ConcreteFieldOpsV1.concreteFieldOps (MP x.1) (MP x.2))
    (fun first2 => cSuffix3 terms (x,first2))
    (fun first2 => pSuffix3 (AspisR1S9CandidateFoldMapPrimitivesV1.mapArray MP terms) (M1 x,first2))
    (AspisR1S9CandidateHelperBridgeV1.map_wide_add x.1 x.2)
    (by intro first2; exact suffix3_maps terms (x,first2))

theorem suffix1_maps (terms : CA) (x0 : C) :
    AspisR1S9CandidateFoldMapPrimitivesV1.mapResult Mout (cSuffix1 terms x0) =
      pSuffix1 (AspisR1S9CandidateFoldMapPrimitivesV1.mapArray MP terms) (MP x0) := by
  unfold cSuffix1 pSuffix1
  apply AspisR1S9CandidateFoldMapPrimitivesV1.mapResult_bind_congr Mout MP
    (Array.index_usize terms 1#usize)
    (Array.index_usize (AspisR1S9CandidateFoldMapPrimitivesV1.mapArray MP terms) 1#usize)
    (fun x1 => cSuffix2 terms (x0,x1))
    (fun x1 => pSuffix2 (AspisR1S9CandidateFoldMapPrimitivesV1.mapArray MP terms) (MP x0,x1))
    (AspisR1S9CandidateFoldMapPrimitivesV1.mapArray_index_result MP terms 1#usize)
    (by intro x1; exact suffix2_maps terms (x0,x1))

theorem candidate_four_term_sums_maps (terms : CA) :
    AspisR1S9CandidateFoldMapPrimitivesV1.mapResult Mout (candidateFourTermSums terms) =
      p6FourTermSums (AspisR1S9CandidateFoldMapPrimitivesV1.mapArray MP terms) := by
  unfold candidateFourTermSums p6FourTermSums
  apply AspisR1S9CandidateFoldMapPrimitivesV1.mapResult_bind_congr Mout MP
    (Array.index_usize terms 0#usize)
    (Array.index_usize (AspisR1S9CandidateFoldMapPrimitivesV1.mapArray MP terms) 0#usize)
    (fun x0 => cSuffix1 terms x0)
    (fun x0 => pSuffix1 (AspisR1S9CandidateFoldMapPrimitivesV1.mapArray MP terms) x0)
    (AspisR1S9CandidateFoldMapPrimitivesV1.mapArray_index_result MP terms 0#usize)
    (by intro x0; exact suffix1_maps terms x0)

#print axioms AspisR1S9CandidateTermStagesComposeV1.suffix6_maps
#print axioms AspisR1S9CandidateTermStagesComposeV1.suffix5_maps
#print axioms AspisR1S9CandidateTermStagesComposeV1.suffix4_maps
#print axioms AspisR1S9CandidateTermStagesComposeV1.suffix3_maps
#print axioms AspisR1S9CandidateTermStagesComposeV1.suffix2_maps
#print axioms AspisR1S9CandidateTermStagesComposeV1.suffix1_maps
#print axioms AspisR1S9CandidateTermStagesComposeV1.candidate_four_term_sums_maps

end AspisR1S9CandidateTermStagesComposeV1
