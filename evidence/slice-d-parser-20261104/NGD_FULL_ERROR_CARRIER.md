# Full wire error carrier

NGD_references.rs.txt declares all eleven deployed r1_wire::Error variants, with identical u8 and usize fields. ActivePole is absent under the deployed feature graph (r1p-check disabled). E002 will extract parse_at_g and its parse_g dependency with this full carrier. No reduced NFU Error carrier is used. An explicit constructor-wise Lean transport and inverse must still be proved before substitution; extraction by itself is not a closure claim.
