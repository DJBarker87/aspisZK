# Failing step

Stage 1, ruling (t) contract-interface calibration: required unimplied caller assertion under `stub_verified` cannot be executed for any of the three foreign Result families. NHD_K004/K008/K012 fail at code generation: the exact Result type does not implement kani::Arbitrary. These are compiler errors, not matched semantic FAILs. The corresponding real-body assertions PASS (K003/K007/K011), and undeclared local writes are detected (K005/K009/K013).

Classification: tool/interface limit; no native/model mismatch, no shipped-code defect, no new trust. The mandatory gate stays OPEN. Subsequent packet closure may not silently substitute pure Bool observation or a different error carrier. The exact next shared deliverable requires a lead-approved calibration/composition interface or tool support for the actual foreign Result types. Ruling (y') permits provenance-preserving ordinary stubs for borrowed children, but does not state that such a stub substitutes for this job's explicit `stub_verified` calibration requirement.

Independent Lean-only obligations continue. No unchanged timeout or memory failure is resubmitted.

Further isolated attempts:

- K034: borrowed-input, full-result/full-frame data_len wrapper times out (90s harness limit, 6,350,116 KiB peak RSS, swap 0). Split into actual enum-clone value pairs K014..017 and clone-substituted transport K046. K046 is a compiler ICE (`missing value for assoc item in impl`, core/src/array/mod.rs:465). No larger cap or unchanged timeout retry.
- K039: actual lib::error with arbitrary-byte log-window assertion and Bool full-frame observation still times out. The eight fixed-writer Debug-label pairs K018..033 omit heap String and syscall transport, and remain unadmitted/K2-unresolved. No repeated heap formatter shape is launched under another label.
- K045: authenticate_asq8_accounts wrong-count prefix over variable 0..8-count prestate times out; its deeper children are not silently stubbed. No control is credited from this timeout.
- K040: own expected Pool default byte was incorrectly written as 0x33. Frozen source says 0x41. K044 repairs the assertion without renaming the harness and passes; K041 remains its failing wrong-value control. This is an input correction, not a compiler or deployed-code mismatch. L009 inventory used the same wrong search marker and is retained; the corrected inspection is a separate source version.

K047's new Bool observation also hit the compiler ICE while the unused trait-stub registrations were present. Removing those registrations (own harness change, not a tool repair) allowed K048 to compile; the separate Bool transport then timed out. This source change and both outcomes are retained, not described as an unchanged retry. Clone oracles are unused in the final harness configuration.

Exact nominal-signature controls K049..057 confirm the same obstruction for metadata's five arguments, the OwnedAccount readonly receiver, and the borrowed OwnedAccount data receiver. Real-body controls PASS and local modifies mutants FAIL; all three stub_verified controls are compile errors, not semantic failures. Auxiliary weak-contract inversion controls K058..060 FAIL as intended.

L015 used ControlFlow's type parameters in the wrong order in a new association statement. L016 corrects that local type error against the actual emitted signature and proves both increment and association with standard axioms. Failed elaborations are never imported as evidence.
