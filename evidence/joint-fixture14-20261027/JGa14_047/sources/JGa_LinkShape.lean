import FIq_Native14
import JFy_Steps
set_option autoImplicit false
namespace AspisR1.JGa_LinkShape
open Aeneas Aeneas.Std Result FIq_Native
open pool_v1.pair_forest_copy_terminal

def Endpoint (e : CompiledPoolV1PairForestEndpoint) : Prop :=
  e.row.val<1024 ∧ e.slot.val<2 ∧ e.pattern.val<14

def Good (l : CompiledPoolV1PairForestLink) : Prop :=
  Endpoint l.producer ∧ Endpoint l.consumer ∧ l.tag.val<2147483647 ∧
    l.weight_kind.val≤4 ∧ l.weight_level.val<64

end AspisR1.JGa_LinkShape
