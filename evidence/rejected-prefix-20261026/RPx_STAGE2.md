# Stage 2: actual top composition and boundary counterexample

RPx_Top.deployed (012) has byte-identical Rc7 input binders, its entire
original conclusion, and RPx_Transport.Claims as an extra conclusion.
No hypothesis is removed or hidden. L181 is deployment-only, not an actual
Rc7 argument. Zero premise-removal credit is claimed.

RPx_RuntimePrefix (008), RPx_Fresh (011), RPx_Duplicates (013), and
RPx_Obstruction (016) establish a concrete interface obstruction: for any
runtime satisfying the actual StoredCarrierBinding, prepend n distinct
addresses (unary-length byte strings). The new runtime has the SAME returned
run in every world, satisfies that SAME binding, preserves any accepted
observation, has exactly n additional query occurrences, and at least n
first reads. Taking n=Q+2966 exceeds Q+2965. This is an interface/model
counterexample, NOT a shipped implementation counterexample. Arbitrary
rejected native/runtime histories cannot be bounded from this binding alone.
No source omission or revised security constant has been established.

RPx_Checkpoint (015) separately verifies all six repeated physical reads,
with exactly the same first-read count as the three-address triple.

Independent continuation: prove the original-account GExq wrapper's
all-outcome Q0+Q1+1921 envelope, including SDK error/copy/cleanup branches,
and retain attempted addresses even when the syscall itself fails. This
addresses GExq's explicitly recorded whole-account-budget gap; it does not
assume its still-missing original-account/F3X association.022 hit default
heartbeats in a generic child proof; split generic lowering (023) from
child cases (030), with explicit irreducibility. No cap/heartbeat increase
or unchanged timeout rerun. Other development errors are retained in receipts.
All successful new theorem audits use only the three standard axioms.
