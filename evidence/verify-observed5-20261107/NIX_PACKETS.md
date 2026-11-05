# NIX outside-slice packets

Target not yet established. F2 and F3 are OPEN; no native/model packet has been admitted.

F2: frozen core/r0/heap.rs::uninit uses try_reserve_exact(1), set_len(1), into_boxed_slice, into_raw/from_raw. Allocation failure maps to Error::Allocation; payload MaybeUninit has no destructor. claims129 writes rows0..2 and may return at each decode error, so initialized-prefix payload and allocation cleanup must be tracked on the SAME allocation. Scalar preflight is not the arbitrary allocator-prestate/claims-type certificate. K001 fails compilation on KMX allocator_api feature; L004 repairs only that scratch input.

F3: secure_circle_point_from_parameter computes square, ONE+square, try_inv, then x/y products; full error SingularParameter. secure_ood calls it FIRST then rejects c1==ZERO with ParameterInCm31Subfield. fallback uses parameters[sample%2], returns map reply or (ONE,ZERO); circle_sample uses qm31_sample then fallback on either error and circle_validated must prove row dispatch and SAME block. Products stay opaque/Lean-discharged, never evaluated in Kani. Q inv/neg/square/try_inv remain imported CLOSED packets, no automatic caller credit.

KMX patch pinned by NIX_KMX.patch, identical to evidence/kani-mitig-20261028/KMX_copy_stubs.patch; applied in scratch only. Matched controls are required before any copy-dependent credit.
