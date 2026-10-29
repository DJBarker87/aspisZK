import PV_B3P_DigestReadSuffix900227
import PV_B3P_DigestBridge8227
namespace PV_B3P_Binding9227
open Aeneas Aeneas.Std PV_B3P_227
open PV_B3P_Success227
set_option autoImplicit false

theorem public_digest_read_binding9 (public1 : reference_terminal.SemanticPublic)
    (openings : aspis_statement.state_only_poseidon.StateOnlyPoseidonOpenings)
    (selectors : reference_copy_terminal.Selectors) :
    reference_terminal.public_digest_lanes public1 openings selectors =
      digest_direct_suffix9_00 public1 openings selectors :=
  (digest_factor8 public1 openings selectors).trans
    (digest_suffix_read_binding9_00 public1 openings selectors)
#print axioms public_digest_read_binding9
end PV_B3P_Binding9227
