# Result-shaped contract audit hold

The initial constructor packet did not explicitly replay the three ruling-(t) fidelity controls for Result<FibreIndex,r0::Error>. Its local claim is held OPEN pending this audit. K003/K004 establish the native constructor value/rejection property but do not by themselves complete the Result-shape fidelity triad. No composed row had been promoted.

The new controls use the exact Result carrier, not a Boolean surrogate: an inverted constructor ensures; a weak valid-Result contract whose real body preserves the input payload but whose replacement need not; and a permitted-cell/forbidden-cell modifies pair. All use the official KMX patch, the frozen core graph offline and unchanged lock checks. A timeout or unsupported construct earns no credit.

K040 PASS/K041 inverted ensures FAIL; K042 weak contract PASS/K043 inverted weak FAIL; K044 real caller PASS. K045 is a COMPILATION ERROR (Result lacks Arbitrary), NOT a valid failing control. The initial own batch classifier checked exit status but missed this distinction; its record is retained and superseded. K046 frame PASS/K047 fails exactly the forbidden-cell assignability check; K048 copy PASS/K049 negative copy FAIL.

Own-input repair: cfg(kani) Arbitrary implementations cover every valid FibreIndex (i<FIBRE_COUNT) and all seventeen Error alternatives. This enables contract-return havoc without weakening native validation. Re-run real/replacement callers with a stricter classifier requiring a verified assertion failure, no compiler error and no timeout. No launcher, Kani library or lead validator was edited.

Audit resolved: K050 real caller PASS; K051 verified replacement FAILS the precise v.get()==i assertion (native compile succeeds, no timeout). Together with K040/K041, K042/K043, K046/K047 and K048/K049 this completes the Result-shape triad and matched controls. K045 remains excluded. The local constructor packet is restored, with the same successful-index model domain and all-usize native rejection behavior. Core-only r0 helper compilation reaches no verifier body; the frozen index macro has no deployed-feature-dependent body or bound.
