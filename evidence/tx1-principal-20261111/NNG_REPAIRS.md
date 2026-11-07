# Own client provenance

NNG_run.py derives from committed NMP_run.py with prefix, workspace and job budget substitutions only. Its offload scope count is stricter than codex-only. NNG_stage.py derives from NMP_stage.py with prefix and verify_finish root selection. Shared reservation, launcher and shim are unchanged. Frozen payload copied byte-for-byte; checks remain active.

L003 failed on generated impl_def capturing NNG_call_3 as a free variable (compiler panic followed the kernel rejection). Changed shape: ordinary explicitly parameterized equality trait, with its ne field expanded to the exact trait-default body; only the sole trait use gains the explicit argument. No semantic root or pass is claimed from L003. Raw generated input unchanged.
