import PV_B3P_LinkDefinitions13227
namespace PV_B3P_Selector49Observation13227
open Aeneas Aeneas.Std PV_B3P_227 PV_B3P_Links13227
-- VM observation of the exact unchanged target. No large kernel reduction.
def point50 : Array aspis_core.field.QM31 10#usize :=
  Array.make 10#usize [aspis_core.field.QM31.ONE,aspis_core.field.QM31.ONE,
    aspis_core.field.QM31.ZERO,aspis_core.field.QM31.ZERO,aspis_core.field.QM31.ONE,
    aspis_core.field.QM31.ZERO,aspis_core.field.QM31.ZERO,aspis_core.field.QM31.ZERO,
    aspis_core.field.QM31.ZERO,aspis_core.field.QM31.ZERO]
def block_words : String := match selector_reference13 point50 with
  | .ok s => reprStr [s.block.c0.a.val,s.block.c0.b.val,s.block.c1.a.val,s.block.c1.b.val]
  | .fail _ => "FAIL"
  | .div => "DIV"
#eval "candidate57_block=" ++ block_words
end PV_B3P_Selector49Observation13227
