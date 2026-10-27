# Grouped inactive contraction: values on original byte operands

FJc_FieldValue.value proves every native field read at index<64 decodes the
SAME32 final-message bytes. Wrapping offsets are proved exact within that
bound (FJc_FieldOffsets). FJc_InactiveCoefficientsValue.sixtyfour proves every
returned group coefficient equals precisely its accumulated decoded fields.
FJc_InactiveValue.value composes this with the native subset/contraction proofs:
for the ORIGINAL f and low, the returned native value equals the pure twelve-
group sum (with source table data and strict byte-codec fields).

No input/output value law is assumed in that composed theorem. Low canonicality
is still an explicit local input, to be derived from the SAME powers/low call.
The fixed table's model-row correspondence and model dualFold transport remain.
This is not yet a complete inactive Pair meaning and earns no top-row removal.

Passing037-family replacement040, source field043, array update045, coefficient
model046/step048/zeros051/loop053, final value054; diagnostic038 passed.
Failures037,039,041,042,044,047,049,050,052 are retained with exact sources.
Every successful theorem audit standard-only; all receipt fields/caps retained.
Charged54/100 Lean;0/20 Kani.0/7 model meanings; top unchanged.
