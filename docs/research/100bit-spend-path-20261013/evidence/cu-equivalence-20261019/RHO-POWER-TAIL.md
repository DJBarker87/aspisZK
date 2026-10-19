# Actual rho power/counter suffix

Candidate 12 remains **incomplete**. This is a source invariant component,
not a whole-candidate equivalence claim.

The original parent and candidate use the byte-identical suffix
`a.power=a.power.mul(p.rho);a.next+=1;`. The extraction kit factors exactly
these bytes with the original complete Prepared and Accumulator declarations.
The raw emitted Types and Funs are promoted unchanged. The single external
operation binds to the existing extracted QM31 multiplication with invertible
coordinate transport; its Rust body is identical in the original arithmetic
extraction, exact candidate, and exact parent. No template axiom is imported.

`CuSavingsRhoPowerTail.source_success` proves that canonical input power and
rho, with entry counter <22, make the complete source suffix succeed. It
derives canonical output power, the exact modular product, counter increment
and bound ≤22, and unchanged weights/rhs. No multiplication/addition-success
premise is supplied. `source_outcome` retains the entire outcome without the
canonicality/bound premises, including errors/divergence.

Focused targets and axioms checks pass. `RHO-POWER-TAIL.json` contains exact
source/object/command/receipt pins and wall/RSS/swap metrics. Only standard
propext/Classical.choice/Quot.sound occur. The existing multiplication proof
was re-pinned in Lean4.32 because the available old source receipt used 4.31;
its new object hash equals the already consumed 4.32 object. No full regression
or dependent replay was needed. The initial source extraction was rejected
before compilation for undeclared Cargo feature names; the corrected kit
retains the original declared features. The first local tail proof failed on
an unreduced record projection and pure-return bind; corrected focused proof
passes. No production Rust changed.

Still required: source caller construction/resume dataflow establishing
canonical input power/rho and range bounds; composition with the coefficient
loop and RHS update; original optimized Option nested-borrow source binding;
sufficient-resource allocation and final transaction observable contexts.
