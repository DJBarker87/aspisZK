# Stage 9: real source zero-binding gates

JFu_PublicBindings.pool_nonzero and domain_nonzero prove the actual source
array comparisons against zero return false on the selected public pool and
deployment-domain bytes. Each source comparison short-circuits at its FIRST
byte (34 versus0 and5 versus0), so no large reduction graph is evaluated.
The array values are tied to the exact retained public ranges by checked
selection theorems. Full decoding and wrapper acceptance remain open.
The uncompiled conditional SnapshotAcceptance candidate is retained ONLY as
JFu_UNCHECKED_SnapshotAcceptance.lean.txt; it is not imported or claimed proved.
