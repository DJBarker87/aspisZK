import PV_B3P_LeadingCell120227
namespace PV_B3P_Binding12227
open Aeneas Aeneas.Std PV_B3P_227 Result
set_option autoImplicit false

theorem leading_pair_packed_binding12
    (openings : aspis_statement.state_only_poseidon.StateOnlyPoseidonOpenings) :
    reference_poseidon.leading_pair_packed openings =
      (PV_B3P_Ordered227.fold (leading_step12 openings.xor12_z)
        [0#usize,1#usize,2#usize,3#usize,4#usize,5#usize,6#usize,7#usize]
        openings.z >>= leading_finish12) :=
  leading_fold12_0 openings openings.z
#print axioms leading_pair_packed_binding12
end PV_B3P_Binding12227
