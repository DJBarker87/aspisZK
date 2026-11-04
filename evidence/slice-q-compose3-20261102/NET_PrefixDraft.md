# Next independent native loop focus

The new NEI commit supplies circle/line fold composed rows; four_dots,
accumulate and prefix-product native state association remain open. Reuse its
committed NEI_PrefixStep/NEI_PrefixWindows proofs rather than duplicating them.

For the prefix native heap gap, split the finite capacity classes that actually
occur in QueryGeometry: flat length 5*N,1<=N<=22. One arbitrary pre-state has
prefixes.len()==index<5*N, capacity5*N; one actual push and one local opaque
product call advance the step. A fixed-capacity allocated raw-word array may
construct this arbitrary valid prior Vec only after checking native M31/u32
layout and initial indexed values. Frame checks sample every old prefix and
input word symbolically. The KMX patch and matching controls are mandatory.
Use the inherited model induction and source-step theorem after each native
window is tied to the actual frozen loop body; never unwind the whole loop.

NET_geometry.rs.txt is an unvalidated draft for the analogous five-word gather
update. It has not been compiled or credited. Prefix and gather are separate
source sites; a final five-word append cannot by itself certify an unobserved
intermediate one-word push.
