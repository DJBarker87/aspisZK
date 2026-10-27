# First-priority seven actual invocation exclusions

op13 / compiler_fence, op16 / default write_all, op17 / File.flush,
op18 / File.write, op85 / r0.Error.fmt, op124 / volatile_clear_cell,
op238 / clear_private_salt remain the inherited support complement.
Their whole-client Result replacement invariance is inherited accepted evidence,
not a new invocation exclusion. No result below promotes that invariant.

The frozen emission contains op17's function in the constructed File.Write
trait record (line 64), op85 in the Error.Debug trait record (315), op124 in
volatile_clear_loop.body (2010), op13 in volatile_clear (2044) and
clear_private_salts (16325), and op238 in the clear_private_salts loop (16296).
A raw constant dependency scan therefore does not itself prove these
exclusions. Creating a closure or constructing a trait record is also not
invoking its members. The required execution certificate must preserve this
distinction and connect the selected field projections/control flow to calls.

The source-supported Result congruence theorem elides unused projections;
the instrumented source-to-invocation soundness statement is still missing.
There is no checked shipped counterexample from this review and it is not a
stop. Continue independent ordered reservation/material control proofs.
