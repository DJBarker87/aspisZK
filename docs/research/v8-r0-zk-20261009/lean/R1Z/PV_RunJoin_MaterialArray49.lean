import R1Z.PV_RunJoin_SourceArray44
import R1Z.PV_RunJoin_FoldCell44
import R1Z.PV_RunJoin_WeightArray46
set_option autoImplicit false
namespace R1Z.PV_RunJoin_MaterialArray49
open Aeneas Aeneas.Std Result ProverRwFull
open ProverCommitWideOps48 ProverCommitMix48
open PV_B2_F_ConstructorCarrier (amap)
theorem arrays (n : Usize) (w : Nat → Raw) :
    PV_RunJoin_BatchRowValue44.array n w=PV_RunJoin_FoldCell44.array n w := rfl

theorem maps (n : Usize) (w : Nat → Raw) :
    amap ProverRwDictionaryTower.fromW (sourceArray n w)=PV_RunJoin_FoldCell44.array n w := by
  exact (PV_RunJoin_SourceArray44.map n w).trans (arrays n w)
#print axioms arrays
#print axioms maps
end R1Z.PV_RunJoin_MaterialArray49
