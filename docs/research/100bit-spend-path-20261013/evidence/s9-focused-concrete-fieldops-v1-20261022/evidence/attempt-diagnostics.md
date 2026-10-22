# Failed focused attempts

1. Initial attempt used `Ops.qmMul` and similar names as projections. Lean rejected those names because `Ops` is a local abbreviation; dependent declarations later printed `sorryAx` as a cascade. No object was produced.
2. Corrected to fully qualified class projections but omitted explicit `@` for the implicit operations-record parameter. Lean reported argument type mismatches. No object was produced.
3. Accepted changed source uses `@AspisR1S9HelperP6.FieldOps.<slot> concreteFieldOps ...`, compiled with exit 0; all audited declarations have only the three standard axioms.
