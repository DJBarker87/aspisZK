import NNY_MerkleRows
import NNY_HeightCongruence
set_option autoImplicit false
noncomputable section
namespace AspisR1.NNY_MerkleShared
open Aeneas Aeneas.Std Result MultiproofConeRef
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open MultiproofConeNodeDomain MultiproofConeNodeIteration MultiproofConeLevelIteration
theorem iterate (D : VTop_Stages.aspis_core.digest.Digest32 Unit) (H : Bytes → State)
 (agree : NodeLeaf D H) (physical : Slice U8) (height : Nat) (s : reference.Scratch)
 (domain : Domain physical s) :
 MultiproofConeLevelIteration.iterate
  (fun s => reference.level_rows (refDigest D) () s physical 0#usize 0#usize) height s =
 MultiproofConeLevelIteration.iterate
  (fun s => reference.level_rows (totalDigest D H) () s physical 0#usize 0#usize) height s :=
 NNY_HeightCongruence.iterate _ _ (Domain physical)
  (fun s hs => level D H agree physical s hs)
  (fun s t hs run => level_preserve (totalDigest D H) () (total D H) physical s t hs run)
  height s domain

theorem height (D : VTop_Stages.aspis_core.digest.Digest32 Unit) (H : Bytes → State)
 (agree : NodeLeaf D H) (physical : Slice U8) (s : reference.Scratch)
 (domain : Domain physical s) :
 reference.levels (refDigest D) () s physical 18#u32 =
 reference.levels (totalDigest D H) () s physical 18#u32 := by
 rw [levels_eq_iteration _ () physical 18#u32 (by decide) s,
  levels_eq_iteration _ () physical 18#u32 (by decide) s]
 exact iterate D H agree physical 18 s domain
#print axioms iterate
#print axioms height
end AspisR1.NNY_MerkleShared
end
