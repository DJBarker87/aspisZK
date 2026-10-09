# R446 rejection-list bridge (component evidence)

This component records the saved successful R446 compile and its direct source dependency chain. It is prepared for combination with the R444/R447 initial-block milestone; it is not a standalone sampler or source-execution claim.

The theorem `run_list` identifies the recursive first-acceptance `run` with a list scan. `decode_value` identifies the alphabet decoder’s accepted value/rejection case, and `sentinel_list` relates a list of `Fin (p+1)` words to the numeric sentinel scan. These are finite mathematical source-shaped definitions only.

The exact source/log/receipt are in `run/`; `manifest.json` records the compile target, source hash, resource limits, metrics, and complete axiom reports. Sources for direct imports are copied in `source/`. Verify the saved package with `python3 verify_evidence.py` from this directory. No compilation was repeated for packaging.
