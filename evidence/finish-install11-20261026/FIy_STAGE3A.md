# Stage (c), first slice: native eight-lane digest binding

FIy_DigestBinding.value checks the ORIGINAL Native08 add_digest_binding /
add_digest_binding_loop with canonicality and all8 decoded updates. It uses
same output,selector,opened,start,expected,right flag. FIy_DigestTarget proves
lane7 right tweak modular addition from checked M31 arithmetic; all other
targets unchanged. FIy_DigestArithmetic proves lift/sub/mul/add values.
FIy_DigestLane/Loop/Closed compose original source with finite range induction
and a symbolic no-double-update closed form. Local bounds remain explicit.

Green044,045,047,048,050,051,052,053.053 targetFIy_DigestBinding.lean exit0,
wall1.4294121470302343s,peak3034368KiB,swap0. Full command/source revision/hash,
deps fingerprint,cgroup,errors and standard-only axioms in receipts.
042 missing unchanged candidate object stopped precompiler (charged); exact
error in042-precompiler-error.json. Replaced by direct native scalar theorem,
not infrastructure repair or unchanged retry. No killed/timed-out proof.
No ten-attempt native-loop reduction stall;0 Kani used.

This is NOT complete public_digest_lanes / frontier20 / carry / public target
meaning. Stage(c) remains open. Full coefficient assembly(d) and all later
Poseidon/link/active/literal meanings remain unopened. Deployed delta0.
