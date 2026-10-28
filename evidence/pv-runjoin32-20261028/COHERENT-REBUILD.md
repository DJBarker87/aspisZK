# Coherent endpoint/lane/native-snapshot dependency rebuild

All1985 dependency modules rebuilt in a fresh private objects directory. The
endpoint audit was excluded from the dependency chunks and checked once after
preflight. h4/SCOPE external objects are read-only; no old project cache fallback
exists in LEAN_PATH. Old runjoin24-lean retained unchanged for provenance.

54 charged build scopes:52 passed,2 rejected. The missing external IR input was
corrected before an isolated pass51301; the explicit RootHelper import fix was
checked alone as51327. Both originals and their exact replacements are retained.
No failed unchanged retry, cap increase, shared write, local Lean or Kani ran.
Peak RSS5391728640bytes; all swaps0. Every module's source/blob/hash, direct
fingerprints, object hash, exit, wall,RSS,swap and axioms are in modules-*.json.

Complete post-build preflight:1985 project objects,4260 direct fingerprints,
5673 external objects and5438 IR companions all match; toolchain and the fresh
objects/external-only prefix match. Current-HEAD h5 source hashes match. The
single import-only source amendment is in SOURCE-RESOLUTION-ADDENDUM.md.

Audits (scope wall; maximum child RSS bytes; swaps):
-51497 endpoint:exit0;2.29s;4338163712;0.
-51498 explicitly imports LaneDenotation31:exit0;2.55s;5031555072;0.
-51499 NativeSnapshot31 preflight:exit0;1.97s;4524470272;0.
All printed axiom sets are subsets of propext,Classical.choice,Quot.sound.
These audits ran once each on the fresh closure. NativeSnapshot31 and the lane
reference theorem have coherent source/object provenance on this closure.
Their native link retains the structural (K-1 substitute) evidence class; finite
comparisons are not promoted to universal native or Kani evidence.

The recorded source-cohort obstruction is resolved for the audited roots. This
does not discharge native runtime/effect/observer or RustRealRefinement premises.
V045/V038 remain proof work; endpoint fields removed/added/weakened/changed0/0/0/0.
T stays exactly entropy_law,entropy_kernel,observation. Privacy target not yet
established. No shipped source, release ELF, key, simulator or observer changed.
