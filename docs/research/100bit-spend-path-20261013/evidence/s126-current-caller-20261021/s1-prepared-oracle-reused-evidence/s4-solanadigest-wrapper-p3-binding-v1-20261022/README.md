# SolanaDigest wrapper binding under P3

This source-only packet connects the focused extracted `SolanaDigest::digest` and `Hash::to_bytes` bodies to the explicit P3 hashv model, then maps the public preparation `Digest32` dictionary to the separately generated current caller `Digest32` dictionary.

The extracted body is transparent and has the operation order `hashv(parts)` followed by `Hash::to_bytes`. The Lean adapter preserves that bind and conversion body. Its only change is to make the external `hashv` callee an explicit parameter. `hashvP3` instantiates that parameter with `ok (sha256 (flatten parts))`. The adapter theorem then matches the existing P3 model. The wrapper and emitted `Copy` implementation, one-field 32-byte `Hash` representation, emitted `to_bytes` body, LLBC, tool binaries, and Cargo dependency sources are pinned in this packet.

The generated `FunsExternal_Template` file is retained under `diagnostics/` to document the extraction boundary. It contains the external hashv axiom and is **not imported** by the accepted Lean source. The accepted module imports only the generated `Types` source and pinned theorem/type owners. Its three named axiom reports are standard Lean axioms only: `[propext, Classical.choice, Quot.sound]`.

The nominal adapter `publicToCurrent` copies the `coremarkerCopyInst` and `digest` fields into `AspisR1CurrentCaller.aspis_core.digest.Digest32`. The theorem states equality with the mapped public model. This makes the dictionary conversion explicit; it does not identify independently generated nominal types by assumption.

Scope limits: P3 is the documented runtime premise that hashv hashes the concatenation of its input slices. The packet does not prove SHA-256, syscall behavior, Solana runtime behavior, or current-pin premise reacceptance. Its SBF/runtime release observation remains pending. The extraction uses the pinned registry dependency set in `source-pins.json`, not an SBF compiler build. The result is a conditional source-wrapper binding under P3, not a complete runtime refinement.

## Validation

`python3 check-kit.py`, `python3 check-llbc.py generated/DigestWrapper-v4.llbc`, `python3 check-functionalized-adapter.py`, and `python3 check_packet.py` validate the exact source cut, emitted body transformation, nonempty error-free LLBC closure, import boundary, compile receipts, named axiom output, and source-only packet contents. The Lean 4.32 focused compile exited 0. The wrapper target took 8.862 s with 3,458,383,872 bytes peak aggregate RSS and zero swaps; the generated types target took 2.311 s with 2,202,550,272 bytes peak aggregate RSS and zero swaps. No Lean object files are included.
