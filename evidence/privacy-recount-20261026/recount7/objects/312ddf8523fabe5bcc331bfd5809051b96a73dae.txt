import R1Z.PV_RunJoin_NodeResult21
import R1Z.PV_RunJoin_AppendNative17
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_AppendShape21
open R0P AspisR1 R0Z.WriterRefine
attribute [local irreducible] nodeCompress poseidonPermutation
local notation "M" => PV_RunJoin_FixtureRecords.M

theorem step_zero (pub : Public M) (hz : pub.nextPairIndex = 0)
    (leaf : Digest M) (n : Fin 20) :
    AppendPath.pathPrefix pub leaf (n.val+1) =
      nodeCompress (AppendPath.pathPrefix pub leaf n.val) (AppendNode.frozenEmpty n.castSucc) := by
  rw [AppendPath.pathPrefix,dif_pos n.isLt,AppendPath.step]
  apply if_pos
  change ((pub.nextPairIndex >>> n.val) &&& 1) = 0
  rw [hz]
  simp only [Nat.zero_shiftRight,Nat.zero_and]
#print axioms step_zero

theorem empty (n : Fin 20) :
    digK (K := M) (PV_Src_CanonicalRoots.table.val[n.val]!) = AppendNode.frozenEmpty n.castSucc := by
  funext i
  exact PV_Src_CanonicalRoots.meaning (K := M) n i
#print axioms empty
end R1Z.PV_RunJoin_AppendShape21
