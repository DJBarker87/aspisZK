# Actual canonical word update under an explicit accumulator bound

PROVED: for every stored U64 raw coordinate and accumulator value below2^46, the exact and/shift-right/wrapping-add fold followed by the actual U64 wrapping accumulation agrees with the natural addition and preserves the intended residue modulo P. The theorem derives no-wrap for that one coordinate update and the folded raw bound from the explicit accumulator bound and the inherent U64 raw bound. It does not assume an abstract wrapping-add agreement law.

The old R22 fold declaration/proof is reused by an exact-body-checked minimal bridge in the canonical root reducer environment. Selected ExtractedCurrentReducer object is16ed0514; old5d2a and old-v6 consumer evidence remain historical and are not co-selected. The source bodies of the two historical reducer versions are identical; compiled dependency environments differ. The port avoids silently mixing objects with one nominal module name.

Three selected focused NUC proof owners pass with standard-only reports, -M4400, High1GiB/Max2GiB/Swap0. Full commands/preflights/times/receipts/axiom logs and immutable source-only worker archive are included. Existing field/reducer/Aeneas and scalar-agreement facts are reused. No source change to production or binaries.

OPEN: derivation of the accumulator bound from actual caller/count (R22 lead assignment); semantics of all raw QM31 product coordinates; actual four-coordinate mutable Dot.push loop and complete caller/runtime. Original unchanged loop lowering failed at InterpBorrows.ml:2731; the failure is retained separately in the worker Dot diagnostics, not accepted as a theorem. This component is compatible with the root current-field and actual Dot/EbyK finish closure but is not a full Dot.push proof.
