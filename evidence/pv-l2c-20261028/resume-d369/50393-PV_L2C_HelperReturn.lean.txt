import PV_L2C_HonestHelper
import PV_L2C_QFold
set_option autoImplicit false
noncomputable section
namespace PV_L2C_HelperReturn
open PV_L2C_NativeQ PV_L2C_QFold

def run (values : List Q) : Option Q :=
  if values.length = 1024 then some (PV_L2C_QBalance.foldQ values zero) else none

theorem expected (table : Fin 1024 → Q) (hc : ∀ r, Canonical (table r))
    (hz : (∑ r, decodeQ (table r)) = 0) : run (List.ofFn table) = some zero := by
  rw [run,List.length_ofFn,if_pos rfl]
  apply congrArg some
  change tableSum table = zero
  apply decode_injective _ _ (tableSum_canonical table hc) zero_canonical
  rw [tableSum_decode table hc,hz,zero_decode]
#print axioms expected

theorem rejects_shape (values : List Q) (hl : values.length ≠ 1024) : run values = none := by
  rw [run,if_neg hl]
#print axioms rejects_shape

open R1Z R0P R0Z.ZkStatement
variable {K : Type} [Field K] [Fintype K] [DecidableEq K]
  [Algebra (ZMod AspisCircleGroupOrder.P) K] [CharP K 2147483647]

theorem honest (F : Subfield K) (B : PackBasis F) (i : PV_L2C_HonestCaller.Family (K:=K))
    (lam chi : K) (project : K →+ (Fin 4 → ZMod PV_L2C_M31.p))
    (table : Fin 1024 → Q) (hc : ∀ r, Canonical (table r))
    (association : ∀ r, decodeQ (table r) = project (R0Z.HonestView.helper
      ((PV_L2C_HonestCaller.source (K:=K)).public i)
      ((PV_L2C_HonestCaller.source (K:=K)).build i) lam chi r)) :
    run (List.ofFn table) = some zero := by
  apply expected table hc
  simp only [association,← map_sum,PV_L2C_HonestHelper.total F B i lam chi,map_zero]
#print axioms honest
end PV_L2C_HelperReturn
