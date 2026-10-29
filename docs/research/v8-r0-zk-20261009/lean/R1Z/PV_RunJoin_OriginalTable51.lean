import R1Z.PV_RunJoin_OriginalLookup51
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_OriginalTable51
open R0Z R0Z.JointView R0Z.FsStatement R1Z.GamesR1 R1Z.TranscriptR1 R1Z.Batched
variable {K CH Aux : Type} [Field K] [Fintype K] [DecidableEq K]
  [Algebra (ZMod AspisCircleGroupOrder.P) K]

theorem member (W : R1Wire K CH Aux) (x : Statement K CH) (V : View K CH Aux R1Bat)
    (c : R1Coins W.Cm W.Tab) (j : TRead) :
    (addr j (recP W x V c.1 c.2.1),c.1 j)∈verLog W x V c := by
  apply List.mem_append_left
  exact List.mem_map.mpr ⟨j,mem_schedule j,rfl⟩

theorem read (W : R1Wire K CH Aux) (x : Statement K CH) (V : View K CH Aux R1Bat)
    (c : R1Coins W.Cm W.Tab) (tab : W.Tab)
    (unique : ((verLog W x V c).map Prod.fst).Nodup) (j : TRead) :
    progOracle W x V c tab (addr j (recP W x V c.1 c.2.1))=c.1 j := by
  unfold progOracle
  rw [PV_RunJoin_OriginalLookup51.lookup _ unique _ _ (member W x V c j)]
#print axioms member
#print axioms read
end R1Z.PV_RunJoin_OriginalTable51
