# Inspection failure isolated; replacement split plan

The shared quiet marker was withdrawn early by its owner. The unchanged shim
then admitted DFm_007, which failed at the fixed Lean -M7000 limit while the
interpreter rendered large declaration Expr values. Exit134, 20.630495230 s,
7,386,260 KiB peak RSS, zero swaps. Original stderr/time and full failed source
are retained. The 17-module inspection is not retried, and no cap is increased.
This was inspection serialization, not parser computation or a failed theorem.

Replacement: eleven independent before/build/after triples (33 remaining
attempts, DFm_008–040). All six direct importers and five dependent consumers
are covered. Each triple audits just one module. The new serializer records
Expr graphs with sharing, not recursively expanded Expr repr strings. Its cache
uses Lean's expression equality; comparison uses SHA-256 of complete node data
and child fingerprints, with exactly the documented alpha/helper renaming.
All source, failed inspection and replacement evidence remain available.

DFm_008–010 already passed: original ExtractedPrefixFieldAgreement inspection,
its source rebuild on the filtered parser overlay, then replacement inspection.
Each uses one 6G/8G/Swap0/Tasks64 scope and -j1 -M7000. No formatter axiom is
accepted, and no top-theorem, premise-removal or release claim is made.
