# Attempt049 mandatory resource review

The combined WeightPoints file rejected the transition join because the loop's
tuple-eliminating lambda was not matched by a projection lambda, then its
whole-tail kernel proof hit excessive memory under-M7000. This source is never
rerun unchanged and never at a higher cap. Its source and diagnostics remain
retained without credit. Replacement:050 contains only the ten-transition join
with the exact source lambda and explicit initial tuple identity; separate
WeightPointTail gives two scalar native subtraction calls and two array updates;
StatementPoints composes those named calls. No full loop or proof/checkpoint
buffer is kernel-reduced. Exact resource receipt retained in049/receipt.json.

053 also reached kernel excessive memory (23.185922701s,RSS7169352KiB,swap0)
at the concrete statement_points header conversion, despite split scalar calls.
It is not rerun unchanged. Replacement: StatementTools normalizes the source
header and exact vector-length/reverse constructor SYMBOLICALLY, on abstract
arrays. StatementPoints then is only a named application of this generic theorem
to the checked loop/scalar/read/write returns. WeightsTools applies the same
preflight pattern to the later weights_new constructor before concrete use.
