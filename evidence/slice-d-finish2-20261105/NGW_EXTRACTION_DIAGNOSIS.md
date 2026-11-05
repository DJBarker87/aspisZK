# E003 predecessor diagnosis and changed attempt

NGM_E003 retained stdout and pins show Charon succeeds, then Aeneas fails at InterpBorrows.ml:2731 while collapsing loop borrow contexts in polynomial_step_ref's mutable indexed array update. No extraction credit exists for E003. The input is NGM_helper_reference.rs.txt (pinned via NGW_INPUTS update).

Replacement NGW_E001 removes the mutable loop, returning a fixed array of eight scalar add_ref applications. point_ref similarly returns four scalar expressions. The reference keeps the same coefficient order and scalar arithmetic; it does not extract a dense polynomial fold or multiply in Rust. Charon/Aeneas binaries, toolchain, offline mode and caps unchanged. A second rejection will select ruling (ah) per cell; no unchanged retry.
