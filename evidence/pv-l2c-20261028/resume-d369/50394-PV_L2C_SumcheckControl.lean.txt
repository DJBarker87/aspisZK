import PV_L2C_HonestSumcheck
set_option autoImplicit false
noncomputable section
namespace PV_L2C_SumcheckControl
open R1Z R0P R0Z.ZkStatement R0Z.PayloadSplit R0Z.RefPayload
variable {K : Type} [Field K] [DecidableEq K]
inductive Failure where
  | boundary : Nat → Failure
  | terminal

def boundary (round : Nat) (poly : Polynomial K) (running : K) : Except Failure Unit :=
  if poly.eval 0 + poly.eval 1 ≠ running then .error (.boundary round) else .ok ()
def terminal (oracle running : K) : Except Failure Unit :=
  if oracle ≠ running then .error .terminal else .ok ()

variable [Fintype K] [Algebra (ZMod AspisCircleGroupOrder.P) K] [CharP K 2147483647]
  {F : Subfield K}

theorem initial (B : PackBasis F) (i : PV_L2C_HonestCaller.Family (K:=K))
    (ch : R0Z.HonestView.Challenges K)
    (hnp : R0Z.HonestValidity.NoPole ((PV_L2C_HonestCaller.source (K:=K)).build i) (ch.sem 0) (ch.sem 1)) :
    boundary 0 (rounds ch 0 (PV_L2C_HonestSumcheck.oracle B i ch))
      (bsumB 10 (fun b => maskLinear BuilderSource.π B (ofBool b)
        ((PV_L2C_HonestCaller.source (K:=K)).build i))) = .ok () := by
  rw [boundary,PV_L2C_HonestSumcheck.initial B i ch hnp,if_neg (by simp)]
#print axioms initial

theorem chained (B : PackBasis F) (i : PV_L2C_HonestCaller.Family (K:=K))
    (ch : R0Z.HonestView.Challenges K) (r : Fin 9) :
    boundary r.succ.val (rounds ch r.succ (PV_L2C_HonestSumcheck.oracle B i ch))
      ((rounds ch r.castSucc (PV_L2C_HonestSumcheck.oracle B i ch)).eval
        (R0Z.HonestView.alpha ch r.castSucc)) = .ok () := by
  rw [boundary,PV_L2C_HonestSumcheck.chain B i ch r,if_neg (by simp)]
#print axioms chained

theorem final (B : PackBasis F) (i : PV_L2C_HonestCaller.Family (K:=K))
    (ch : R0Z.HonestView.Challenges K) :
    terminal (PV_L2C_HonestSumcheck.oracle B i ch (R0Z.HonestView.alpha ch))
      ((rounds ch 9 (PV_L2C_HonestSumcheck.oracle B i ch)).eval (R0Z.HonestView.alpha ch 9)) = .ok () := by
  rw [terminal,PV_L2C_HonestSumcheck.terminal B i ch,if_neg (by simp)]
#print axioms final
end PV_L2C_SumcheckControl
