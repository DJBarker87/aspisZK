# Record parser model focused evidence

The final `R1RecordParserModel` target proves that the modeled list parser succeeds exactly on the mathematical record frame with the stated payload length, and hence equals `RecordFrameCodec.parse` for lengths below `2^32`. The model uses the retained little-endian word codec and `ListFieldCodec.fixedBytes?_sound`; it does not prove correspondence to extracted Rust code.

Attempts b–i are preserved failed Lean drafts; j is the green focused compile. Attempt a stopped before compilation because the staged source basename did not match the wrapper target, and has no receipt. Every available receipt, source snapshot, and source sidecar was hash-checked.
