import PV_B3P_PrefixComplete224
import PV_B3P_HelperComplete224
namespace PV_B3P_HelperCompose224
open Aeneas Aeneas.Std PV_B3P_RustResult PV_B3P_PrefixAction224
set_option autoImplicit false

-- Composition of the two accepted extracted components. Registry generation,
-- trace conversion and native root binding remain separate obligations.
def reference (view : PV_B3P_224Prefix.prefix224.View) (registry : Registry)
    (append_index : U64) (lambda chi : PV_B3P_224.aspis_core.field.QM31) :=
  bindR (PV_B3P_224Prefix.prefix224.copy_rows view registry append_index lambda)
    (fun rows => PV_B3P_224.reference224.from_rows rows chi)

theorem complete_result (view : PV_B3P_224Prefix.prefix224.View) (registry : Registry)
    (append_index : U64) (lambda chi : PV_B3P_224.aspis_core.field.QM31) :
    mapR (fun out : PV_B3P_HelperLoop224.Output => out.val)
        (reference view registry append_index lambda chi) =
      bindR (PV_B3P_HelperState224.run (action view registry append_index lambda)
          0 136 PV_B3P_PrefixComplete224.seed)
        (fun rows => PV_B3P_HelperList224.ordered (PV_B3P_HelperEval224.eval rows chi) 0 1024) := by
  unfold reference
  rw [mapR_bindR,PV_B3P_PrefixComplete224.complete_result]
  congr 1
  funext rows
  exact PV_B3P_HelperComplete224.complete_result rows chi

#print axioms complete_result
end PV_B3P_HelperCompose224
