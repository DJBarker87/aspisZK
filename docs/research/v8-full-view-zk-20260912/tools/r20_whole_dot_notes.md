# R20 whole-dot source-local candidate

`r20_whole_dot.rs` adapts the packet's nine-channel accumulator to the actual
`aspis_core::field::QM31`. It keeps four products per raw channel, folds every
four terms, caps a dot at 4096 terms, and reconstructs the four QM31 limbs once.

`dot` validates every input limb once before accumulation. `push_canonical` is
the private-contract hot path and must only be called after that boundary
check. The candidate does not alter public field types or source stages.

`r20_whole_dot_check.rs` is a standalone differential: scalar QM31 multiply/add
is the oracle, with the existing prepared 3-product and staged 4-product
helpers as controls (the actual field currently exposes no prepared-4 helper).
It covers 512 deterministic vectors across lengths 0, 1, 2, 3, 4, 5, 6, 7,
15, 16, 17, 27, 163, 271, 4095, and 4096, including all-limb-maximal vectors,
eight individual noncanonical-limb controls, direct 4096/4097 accumulator
boundaries, and rejection of mismatched inputs. `r20_dot_micro.rs` is a
no-allocation selector over caller-provided runtime vectors for scalar, existing
4-batches with leftovers, prepared-3 blocks, and whole-dot paths at lengths
3/4/6/16/27/163. The research harness supplies `black_box` inputs/outputs,
timing/CU logging, and equality assertions. No build or protocol/security
conclusion is made here.
