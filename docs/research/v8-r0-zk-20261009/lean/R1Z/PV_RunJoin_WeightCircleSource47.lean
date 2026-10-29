import R1Z.PV_RunJoin_WeightCircleRows46
import R1Z.PV_RunJoin_WeightFactorWriteCps47
import R1Z.PV_RunJoin_WeightFactorRestore47
import R1Z.PV_RunJoin_WeightCellIndices46
set_option autoImplicit false
namespace R1Z.PV_RunJoin_WeightCircleSource47
open Aeneas Aeneas.Std Result
open PV_B2_F_ConstructorCarrier (K)
open PV_B2_C_ConstructorRows (Factors)
open PV_RunJoin_WeightFactorWrite47 (write Matrix)

theorem double (x : K) : PV_B2_C_WeightsNative.host_weights.double x=
    PV_RunJoin_WeightDoubleFactor46.run x := by rfl
#print axioms double

def lines : Nat → Factors → Usize → Usize → K → Result Factors
  | 0,fs,_,_,_ => ok fs
  | n+1,fs,slot,d,x => do
    let y ← PV_RunJoin_WeightDoubleFactor46.run x
    let row ← PV_RunJoin_WeightLineFactor46.run x y
    let fs1 ← write fs slot d row
    let next ← PV_RunJoin_WeightDoubleFactor46.run y
    lines n fs1 slot (Usize.wrapping_add d 1#usize) next

def run (fs : Factors) (slot : Usize) (x y : K) : Result Factors := do
  let row ← PV_RunJoin_WeightCircleFactor46.run x y
  let fs1 ← write fs slot 0#usize row
  let next ← PV_RunJoin_WeightDoubleFactor46.run x
  lines 4 fs1 slot 1#usize next

attribute [local irreducible] PV_B2_C_WeightsNative.host_weights.double
  PV_B2_C_WeightsNative.aspis_core.field.QM31.mul
  PV_B2_C_WeightsNative.aspis_core.field.QM31.add
  PV_B2_C_WeightsNative.aspis_core.field.QM31.sub

theorem row3 (fs : Factors) (z : Array PV_B2_F_ConstructorCarrier.Point 2#usize) :
    PV_B2_C_ConstructorRows.row3 fs z=(do
      let p ← Array.index_usize z 0#usize
      run fs 3#usize p.x p.y) := by
  simp only [PV_B2_C_ConstructorRows.row3,run,lines,
    PV_RunJoin_WeightCircleFactor46.run,PV_RunJoin_WeightLineFactor46.run,
    ←double,PV_RunJoin_WeightFactorWriteCps47.complete,bind_assoc,bind_tc_ok,
    PV_RunJoin_WeightCounters46.add1,PV_RunJoin_WeightCounters46.add2,
    PV_RunJoin_WeightCounters46.add3,PV_RunJoin_WeightCellIndices46.add4]
  simp only [write]
#print axioms row3
end R1Z.PV_RunJoin_WeightCircleSource47
