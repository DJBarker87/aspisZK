# Own runner repairs

Seed preflight 1 failed before admission/launch: owned host directory absent when opening barrier log. Added mkdir(exist_ok=True) before opening the log; reservation and validation unchanged. No Kani/Lean/extraction allocation consumed. Original failure retained in NHP_NATIVE_SEED-initial.log.
