import R1Z.PV_RunJoin_WeightFactorWrite47
set_option autoImplicit false
namespace R1Z.PV_RunJoin_WeightPointRowStages47
open Aeneas Aeneas.Std Result
open PV_B2_F_ConstructorCarrier (K)
open PV_B2_C_ConstructorRows (Factors Points)
open PV_RunJoin_WeightFactorWrite47 (write)
abbrev Point := Array K 10#usize

def stage4 (p : Point) (fs : Factors) (slot : Usize) : Result Factors := do
  let a ← Array.index_usize p 7#usize
  let b ← Array.index_usize p 6#usize
  let row ← PV_RunJoin_WeightPointFactor46.run a b
  write fs slot 4#usize row

def stage3 (p : Point) (fs : Factors) (slot : Usize) : Result Factors := do
  let a ← Array.index_usize p 9#usize
  let b ← Array.index_usize p 8#usize
  let row ← PV_RunJoin_WeightPointFactor46.run a b
  let fs1 ← write fs slot 3#usize row
  stage4 p fs1 slot

def stage2 (p : Point) (fs : Factors) (slot : Usize) : Result Factors := do
  let a ← Array.index_usize p 5#usize
  let b ← Array.index_usize p 4#usize
  let row ← PV_RunJoin_WeightPointFactor46.run a b
  let fs1 ← write fs slot 2#usize row
  stage3 p fs1 slot

def stage1 (p : Point) (fs : Factors) (slot : Usize) : Result Factors := do
  let a ← Array.index_usize p 1#usize
  let b ← Array.index_usize p 0#usize
  let row ← PV_RunJoin_WeightPointFactor46.run a b
  let fs1 ← write fs slot 1#usize row
  stage2 p fs1 slot

def stage0 (p : Point) (fs : Factors) (slot : Usize) : Result Factors := do
  let a ← Array.index_usize p 3#usize
  let b ← Array.index_usize p 2#usize
  let row ← PV_RunJoin_WeightPointFactor46.run a b
  let fs1 ← write fs slot 0#usize row
  stage1 p fs1 slot
end R1Z.PV_RunJoin_WeightPointRowStages47
