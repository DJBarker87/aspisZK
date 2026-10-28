import PV_L2C_HonestValidity
import R0Z.RefPayload
import R0Z.PureRounds
set_option autoImplicit false
noncomputable section
namespace PV_L2C_HonestSumcheck
open R1Z R0P R0P.SemSource R0P.SemDegree R0P.Sumcheck
open R0Z.HonestView R0Z.PayloadSplit R0Z.Shift R0Z.RefPayload
open PV_L2C_HonestCaller
variable {K : Type} [Field K] [Fintype K] [DecidableEq K]
  [Algebra (ZMod AspisCircleGroupOrder.P) K] [CharP K 2147483647] {F : Subfield K}

/-- Decoded oracle at the exact honest compiler trace. Association to the
native SemanticOracle and its produced coefficients remains a separate P. -/
def oracle (B : PackBasis F) (i : PV_L2C_HonestCaller.Family (K:=K))
    (ch : Challenges K) : PointFunction K := fun a =>
  maskLinear BuilderSource.π B a ((source (K:=K)).build i)+
    fOrig ((source (K:=K)).public i) B ch
      (actual ((source (K:=K)).public i) B ((source (K:=K)).build i) ch 0) a

theorem degree (B : PackBasis F) (i : PV_L2C_HonestCaller.Family (K:=K)) (ch : Challenges K) :
    VDeg 10 (fun _ => 27) (oracle B i ch) :=
  vdeg_add (maskLinear_vdeg _ B _) (vdeg_fOrig _ B ch _)
#print axioms degree

theorem initial (B : PackBasis F) (i : PV_L2C_HonestCaller.Family (K:=K)) (ch : Challenges K)
    (hnp : R0Z.HonestValidity.NoPole ((source (K:=K)).build i) (ch.sem 0) (ch.sem 1)) :
    (rounds ch 0 (oracle B i ch)).eval 0+(rounds ch 0 (oracle B i ch)).eval 1=
      bsumB 10 (fun b => maskLinear BuilderSource.π B (ofBool b) ((source (K:=K)).build i)) := by
  rw [R0Z.Chain.rounds_initial ch _ (degree B i ch)]
  change bsumB 10 (fun b => maskLinear BuilderSource.π B (ofBool b) ((source (K:=K)).build i)+
    fOrig ((source (K:=K)).public i) B ch
      (actual ((source (K:=K)).public i) B ((source (K:=K)).build i) ch 0) (ofBool b))=_
  rw [bsumB_add,R0Z.HonestValid.bsum_fOrig_zero _ B _ ch
    (PV_L2C_HonestValidity.valid F B i ch hnp),add_zero]
#print axioms initial

theorem chain (B : PackBasis F) (i : PV_L2C_HonestCaller.Family (K:=K)) (ch : Challenges K)
    (r : Fin 9) :
    (rounds ch r.succ (oracle B i ch)).eval 0+(rounds ch r.succ (oracle B i ch)).eval 1=
      (rounds ch r.castSucc (oracle B i ch)).eval (alpha ch r.castSucc) :=
  R0Z.Chain.rounds_chain ch _ (degree B i ch) r
#print axioms chain

theorem terminal (B : PackBasis F) (i : PV_L2C_HonestCaller.Family (K:=K)) (ch : Challenges K) :
    (rounds ch 9 (oracle B i ch)).eval (alpha ch 9)=oracle B i ch (alpha ch) :=
  eval_rounds_nine ch _ (degree B i ch)
#print axioms terminal
end PV_L2C_HonestSumcheck
