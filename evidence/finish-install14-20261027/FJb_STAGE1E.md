# Stage 1E: original native columns and final-row value

FJb_WideSum4.value048 derives exact scalar addition and a2^34 bound.
FJb_ColumnIndices049/ColumnCell052 derive actual four selected source limbs.
FJb_BuilderSelected055/BuilderTotal056 derive selected ordered constructor
cells and constructor success from proven total stable callbacks.
FJb_ColumnRow057/ColumnTable059 prove ALL16 native table values and bounds on
the SAME stage state and original constructors. FJb_MaskColumn064 proves the
native mask index modulo4 symbolically. FJb_RawValue063 proves all native
raw-limb reductions preserve field value. FJb_TailCell065 and TailRow067 prove
actual final external row callbacks and decode(q)+decode(selected sum column),
with output canonicality. No separately chosen table/output is an input premise.

067:exit0,wall1.7000222809729166s,peak3860716KiB,swap0,standard axioms only.
All above passing modules print subsets of propext/Classical.choice/Quot.sound.
FJb_MatrixLocality054/GroupedValues061/GroupedFold062 prove distinct-group
sparsity and the whole four-group source fold formula symbolically.

050/051/058 were tuple/do notation elaboration problems,corrected052/059.
053/060 and066/068 were finite-index transparency/dependent rewrite errors;
passing replacements use typed finite-index equality/congruence,not numeral
normalization or larger limits.068 is still superseded by the pending focused
ColumnBound fix at this stage. No wall timeout,memory kill or cap change.
No deployed premise removed. Exact remaining blockers are inOBSTRUCTION70.
