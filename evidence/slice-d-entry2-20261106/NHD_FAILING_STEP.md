# Failing step

Stage 1, ruling (t) contract-interface calibration: required unimplied caller assertion under `stub_verified` cannot be executed for any of the three foreign Result families. NHD_K004/K008/K012 fail at code generation: the exact Result type does not implement kani::Arbitrary. These are compiler errors, not matched semantic FAILs. The corresponding real-body assertions PASS (K003/K007/K011), and undeclared local writes are detected (K005/K009/K013).

Classification: tool/interface limit; no native/model mismatch, no shipped-code defect, no new trust. The mandatory gate stays OPEN. Subsequent packet closure may not silently substitute pure Bool observation or a different error carrier. The exact next shared deliverable requires a lead-approved calibration/composition interface or tool support for the actual foreign Result types. Ruling (y') permits provenance-preserving ordinary stubs for borrowed children, but does not state that such a stub substitutes for this job's explicit `stub_verified` calibration requirement.

Independent Lean-only obligations continue. No unchanged timeout or memory failure is resubmitted.
