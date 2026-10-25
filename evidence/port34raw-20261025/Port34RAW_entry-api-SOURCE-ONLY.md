# Entry-point diagnosis — source only

Call360 line156 used `liftIO runDiagnostic` in namespace Port34RAW with only
`open Lean`. Public Lean4.32 source Command.lean line18 opens namespace
Lean.Elab.Command and line222 defines liftIO : IO α → CommandElabM α.
The missing namespace explains the reported unknown identifier. Proposed entry:

```lean
run_cmd do
  Lean.Elab.Command.liftIO runDiagnostic
```

Complete UNCOMPILED corrected snapshot retained separately; executed source is
unchanged. Text inspection only, no361, helper, parse check, warmup or proof.
The prior raw function's successful elaboration is not successful execution.
No claim that this correction passes a compiler or avoids all later errors.
Text preflight failed to check this identifier's namespace; its PASS did not
promise compiler success. Future preflight should demand the qualified public
entry. New compiler allocation is required to obtain any actual raw data.

The noncompiler RLIMIT_RSS preflight attempt also failed without a Lean charge;
macOS reported an invalid limit despite infinity/infinity. It was removed rather
than raising caps. Bounded noncompiler work used measured512MiB checks; source
analysis peaked19,005,440B. No host or systemd scope was launched.

Public API pin: {
  "path": "/Users/dominic/.elan/toolchains/leanprover--lean4---v4.32.0/src/lean/Lean/Elab/Command.lean",
  "bytes": 39429,
  "sha256": "6e04aef09ca96afa8464856ea5775136d1152360df0b6a41fe81bef035c9d609"
}
