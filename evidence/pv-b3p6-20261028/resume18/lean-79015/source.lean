import PV_B3P_NativePublicDigest15227
import PV_B3P_LinkDefinitions13227
namespace PV_B3P_Association547227
open Aeneas Aeneas.Std PV_B3P_227 PV_B3P_Links13227 PV_B3P_Native15227
set_option autoImplicit false

/-- Full Result equality for the ordered source digest stages and level loop. -/
theorem public_digest_source_link547 :
    PV_B3P_Link_terminal_public_digest_lanes native_public_digest15 :=
  funext fun public1 => funext fun openings => funext fun selectors =>
    native_public_digest_binding15 public1 openings selectors

#print axioms public_digest_source_link547
end PV_B3P_Association547227
