import PV_B3P_ScheduleCaller15227
import PV_B3P_LinkDefinitions13227
namespace PV_B3P_Association546227
open Aeneas Aeneas.Std PV_B3P_227 PV_B3P_Links13227 PV_B3P_Native15227
set_option autoImplicit false

theorem schedule_source_link546 : PV_B3P_Link_terminal_add_schedule_lanes native_schedule15 :=
  funext fun packed => funext fun pub => funext fun openings => funext fun selectors =>
    native_schedule_binding15 packed pub openings selectors

#print axioms schedule_source_link546
end PV_B3P_Association546227
