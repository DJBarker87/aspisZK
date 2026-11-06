# Own input-client repairs

Inherited NKI client renamed privately to NKR; budget140Lean/70Kani/0extraction,own workspace/target, same admission+caps+transport+disk policy. NKI seed first,NKN second, hashes/bytes checked before each scope. NKN inherited dependency paths added after L001; no infrastructure change.

Native own-input hash changes are staged only by committed exact delta patches with git apply --check, then all frozen/source/graph/lock checks remain. K003 validation stopped before Kani after missing upload of first delta; K011 corrected the required input manifest. Original K003 retained.

Required validation-input existence is now asserted (previous inherited code silently omitted absent entries). Queue scheduling now checks every direct NKR import plus explicit prerequisites against current source-hash-matched passing receipts, preventing missing-object prelaunch mistakes such as L038/L063/L076. No test or source check weakened.

All scopes use existing unchanged S2W_run_host.py and existing reservation script; no launcher/shim/monitor infrastructure modified.
