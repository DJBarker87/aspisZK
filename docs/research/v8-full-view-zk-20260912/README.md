# V8 full-view privacy workstream

This directory is the isolated privacy workstream for the repaired,
transfer-only positive COMPLETE profile at
`9e432896a4e1515efebe940b71fd9b4f9f009189`.

The current milestone is deliberately narrow:

- the pack's 24 Python diagnostics pass when invoked directly;
- the consecutive-q22 separator is reproduced by the actual Rust encoder,
  conditional on the separately reconstructed repaired inventory/balancing
  rule;
- source inspection shows that the generated positive-V8 path does not call
  the repository's q18 Spend rank gate;
- generic Lean algebra and the pinned FS cache helper compile after
  API/import-only repairs.

This is not a proof of V8 zero knowledge and not a demonstrated valid-payment
privacy attack. See [CURRENT_STATUS.md](CURRENT_STATUS.md).
