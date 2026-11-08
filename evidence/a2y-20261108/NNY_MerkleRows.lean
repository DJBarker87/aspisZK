import NNY_MerkleAgreement
set_option autoImplicit false
noncomputable section
namespace AspisR1.NNY_MerkleShared
open Aeneas Aeneas.Std Result MultiproofConeRef
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open MultiproofConeNodeDomain MultiproofConeNodeIteration MultiproofConeLevelIteration
/-- Source recursion follows total auxiliary progress, but uses only node-shape agreement. -/
theorem rows (D : VTop_Stages.aspis_core.digest.Digest32 Unit) (H : Bytes → State)
 (agree : NodeLeaf D H) (physical : Slice U8) (fuel : Nat)
 (s : reference.Scratch) (i w : Usize) (domain : RowDomain physical s i w)
 (bound : s.n.val-i.val ≤ fuel) :
 reference.level_rows (refDigest D) () s physical i w =
 reference.level_rows (totalDigest D H) () s physical i w := by
 induction fuel generalizing s i w with
 | zero =>
   have halt : i≥s.n := by obtain ⟨_,_,_,_,_⟩ := domain; scalar_tac
   rw [reference.level_rows,reference.level_rows]
   simp only [halt,if_true]
 | succ fuel ih =>
   rw [reference.level_rows,reference.level_rows]
   by_cases halt : i≥s.n
   · simp only [halt,if_true]
   · simp only [halt,if_false,node D H agree]
     obtain ⟨out,eqout,post⟩ := binary_step_progress (totalDigest D H) () (total D H)
      physical s i w domain (by scalar_tac)
     rw [eqout]
     simp only [bind_tc_ok]
     cases out with
     | Stop stopped => rfl
     | Next next ni nw =>
       obtain ⟨sameN,nextDomain,advance,_⟩ := post
       exact ih next ni nw nextDomain (by rw [sameN];omega)
theorem level (D : VTop_Stages.aspis_core.digest.Digest32 Unit) (H : Bytes → State)
 (agree : NodeLeaf D H) (physical : Slice U8) (s : reference.Scratch)
 (domain : Domain physical s) :
 reference.level_rows (refDigest D) () s physical 0#usize 0#usize =
 reference.level_rows (totalDigest D H) () s physical 0#usize 0#usize :=
 rows D H agree physical s.n.val s _ _ ⟨domain.1,domain.2.1,by simp,by simp,domain.2.2⟩ (by simp)
#print axioms rows
#print axioms level
end AspisR1.NNY_MerkleShared
end
