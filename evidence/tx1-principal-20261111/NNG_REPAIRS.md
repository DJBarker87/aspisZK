# Own client provenance

NNG_run.py derives from committed NMP_run.py with prefix, workspace and job budget substitutions only. Its offload scope count is stricter than codex-only. NNG_stage.py derives from NMP_stage.py with prefix and verify_finish root selection. Shared reservation, launcher and shim are unchanged. Frozen payload copied byte-for-byte; checks remain active.
