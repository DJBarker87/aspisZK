# Concrete adapter for the S9 explicit-helper candidate

PROVED: the six candidate field-operation wrappers preserve the entire Result, including failure and divergence, under explicit invertible carrier maps to the selected existing concrete FieldOps. The generated Types, external-operation implementation and helper compile. A transitive audit of the helper, scalar factor and actual generated Std iterator fold reports only propext, Classical.choice and Quot.sound; none of the six raw template axioms is imported.

The raw Aeneas diagnostic files are retained separately under candidate-adapter/raw-aeneas-diagnostic and are not accepted sources. The accepted external-operation file installs concrete definitions instead of raw opaque axioms. Generated option overrides are removed. The only other generated-helper change mechanically fully qualifies namespace references shadowed by a local variable; candidate-adapter/check_adapter.py compares that transformation against raw output.

This is a local extracted candidate cut. Compilation is not a proof of the helper’s full arithmetic specification, its enclosing caller, all actual Rust library semantics, a final artifact join, adoption, or 100-bit soundness. The source candidate remains separate from production. Actual selected field-operation correspondence reuses the existing owner and its source obligations; those are not discharged merely by the carrier adapter.

Validation: focused targets only, one local compiler at a time, -j1 -M4400, recorded mutex/RSS watchdog, observed zero swaps. Per-stage receipts record source revision, source/object hashes, wall time and RSS. The source audit reuses these compiled modules; there was no package or final closure replay. No compiled objects or deployment keys are included.

Run `python3 -B check_packet.py` for retained-receipt integrity and `python3 -B candidate-adapter/check_adapter.py` for the source transformation.
