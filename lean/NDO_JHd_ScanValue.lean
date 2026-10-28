import NDO_JHb_Header
import AdapterRwModel
set_option autoImplicit false
namespace AspisR1.JHd_ScanValue
open Aeneas Aeneas.Std Result

def candidate : AdapterRw.aspis_statement.pool_v1.pair_terminal.PoolV1PairVerifiedAfterstateV1 :=
  ⟨JFt_AfterstateValue.value.next_pair_index,JFt_AfterstateValue.value.next_root,
    JFt_AfterstateValue.value.next_frontier⟩
def value : AdapterRw.r1_pool_adapter.ScannedAsqaProof := ⟨candidate,57607#usize⟩
theorem length : value.proof_length=57607#usize := rfl
#print axioms length
end AspisR1.JHd_ScanValue
