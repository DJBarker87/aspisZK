import NMT_345Dec_T4
import NFY_Part058
set_option autoImplicit false
noncomputable section
namespace NMT_345Dec
open Aeneas Aeneas.Std AspisR1.NMT_Transport
def toT5 (x : NMT_stage1_owned.aspis_statement.pool_v1.pair_terminal.PoolV1PairVerifiedAfterstateV1) : AspisR1TerminalDecoder.pool_v1.pair_terminal.PoolV1PairVerifiedAfterstateV1 :=
 ⟨x.next_pair_index,x.next_root,x.next_frontier⟩
def fromT5 (x : AspisR1TerminalDecoder.pool_v1.pair_terminal.PoolV1PairVerifiedAfterstateV1) : NMT_stage1_owned.aspis_statement.pool_v1.pair_terminal.PoolV1PairVerifiedAfterstateV1 :=
 ⟨x.next_pair_index,x.next_root,x.next_frontier⟩
@[simp] theorem toT5_inverse (x : NMT_stage1_owned.aspis_statement.pool_v1.pair_terminal.PoolV1PairVerifiedAfterstateV1) : fromT5 (toT5 x) = x := by
 cases x <;> simp [toT5,fromT5]
#print axioms toT5_inverse
@[simp] theorem fromT5_inverse (x : AspisR1TerminalDecoder.pool_v1.pair_terminal.PoolV1PairVerifiedAfterstateV1) : toT5 (fromT5 x) = x := by
 cases x <;> simp [fromT5,toT5]
#print axioms fromT5_inverse
end NMT_345Dec
