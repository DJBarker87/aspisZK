import R1Z.PV_RunJoin_CommonOracle51
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_CommonRecord51
open R0P R0Z R0Z.JointView R0Z.FsStatement R0Z.HvzkV
open R1Z.GamesR1 R1Z.GamesR1PBin R1Z.CouplingR1PBin R1Z.TranscriptR1 R1Z.EventsR1PBin
variable {K CH Aux : Type} [Field K] [Fintype K] [DecidableEq K]
  [Algebra (ZMod AspisCircleGroupOrder.P) K] {F : Subfield K}
variable (W : R1Wire K CH Aux) (Pr : R1ProverP K CH Aux F W)
  (h : R0Z.ZkStatement.HonestProver K) (B : PackBasis F)
  (outputs : Statement K CH → Challenges K → Aux) (x : Statement K CH) (w : h.Instance)

def record (v : Pos1 Pr.E₁ Pr.E₂ → OracleAnswer) : Rec :=
  recP W x (view h B outputs x w (chOf W (trOf v)) (tapeR W Pr v)) (trOf v) (rootsOf v)

theorem address (R : RomModel W) (N : Nat) (hN : 0<N)
    (s : Fin N → AttS (F:=F) W Pr) (k : Fin N) (j : TRead) :
    addr j (record W Pr h B outputs x w (s k).2.1)=
      addrQ W Pr R N hN h B outputs x w s (k,.inl j) := rfl

theorem transcript (v : Pos1 Pr.E₁ Pr.E₂ → OracleAnswer) (j : TRead) :
    (record W Pr h B outputs x w v).tr j=v (.inl j) := rfl
#print axioms record
#print axioms address
#print axioms transcript
end R1Z.PV_RunJoin_CommonRecord51
