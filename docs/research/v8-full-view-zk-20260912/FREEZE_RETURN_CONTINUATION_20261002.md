# Freeze return continuation extraction repair

The previous frozen extraction discarded ten nested `?` error returns in the selected freeze loop. The pass trace shows those branches writing LLBC local zero, then joining shared cleanup and a loop break; only a nearby explicit return was lowered into `pending_return`. That left the translated error branches returning `done none`, while successful branches and the outer second-circle error were carried correctly.

An isolated candidate repair tracks syntactically cleanup-only enclosing continuations. It re-exposes a function return after the return-place write only when that continuation reaches a known function return, including a matching loop-break continuation. It tightens the previous unconditional Break rewrite. It preserves the existing drop-as-no-op gate; it does not introduce a new execution axiom or change Rust verifier source.

The candidate translator builds successfully (7.05 seconds, actual Docker cgroup peak 565,026,816 bytes, zero swap), and the same frozen callback translates successfully (4.85 seconds, peak RSS 340,640 KiB, zero swaps). All eleven loop error branches now return their captured error; the loop returns a direct Result. All generated declarations outside freeze_loop.body, freeze_loop and freeze are byte-identical modulo namespace. Complete pass traces, exact before/after extractor source, commands, generated diagnostic copies and checksums are in the [evidence manifest](evidence/freeze-return-continuation-20261002/manifest.json).

This is extraction evidence, not a formal source-execution theorem. No generated external-template axiom was imported or accepted, and the full freeze was not compiled. The two retained tiny after-loop probes were tested once with the changed extractor; both still fail symbolic context joining. Their complete negative evidence is retained. There is no general extractor correctness claim.

Next: faithful standard-library fold and extend execution, then the complete actual freeze and oracle chronology through rho. Privacy and soundness remain unproved. CU results and security parameters are unchanged; no CU benchmark or unchanged regression suite ran.
