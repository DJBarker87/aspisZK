# Contract-interface admission gap

C3-BIN ruling (t) requires the per-shape fidelity controls before relying on a non-Bool/record contract interface. The actual-function contracts return ProgramResult or Result<&[u8], ProgramError>. Their inverted ensures controls fail as intended, but the real-body/unimplied assertion, stub_verified/unimplied assertion, and modifies-violation controls are missing for these interfaces.

This scheduling omission blocks promotion of readonly_meta_ok (TX2:223), require_readonly_account (TX2:236), and OwnedAccount::data (TX1:335/TX2:229). Native passes, full-result ports, matching copy controls, standard axioms, and a clean source scan do not substitute for the missing gate. No candidate is CLOSED. No existing criterion is weakened.

Next worker: calibrate the three recorded interface families under the same toolchain, frozen graph, deployed features, and exact KMX patch; retain the existing inverted controls; obtain a real-body PASS and stub_verified FAIL for an unimplied caller assertion, and a modifies-violation FAIL. Use local old-state records, never writable-static observers. If claiming one calibration covers multiple signatures, provide the exact shape association. All original native runs and their source snapshots remain available for review.

Boolean observer packets cover only subsets (data copied-buffer and borrow-error cases; length copied-buffer; checkpoint non-borrow cases). They are not used to bypass the missing complete interface gate or the unproved cases.
