# Strict second-record decoding bound to the actual returned root array

`ViewParseRootStrictSecondBound.successful_view_round1_strict_second_with_root_binding` starts only from actual successful candidate parser execution and the actual returned two-fold variant. It returns the actual rootArray with `view.folded_root = some rootArray`, identifies the decoded root state as `stateOfBytes (rootBytesOfArray rootArray)`, and proves strict second-record decoding of the frame formed from those exact root-array bytes followed by the exact returned round1 bytes. There is no arbitrary root, root-byte, query-check success, echeck-success or slice-length premise.

The source inversion follows the actual parse_shape two-fold root-present branch, successful32-byte slice-to-array conversion and same returned view. Existing fixed-array length and `PrefixedStateCodec.bytes_stateOfBytes` give the hash-state roundtrip for any32bytes. State is a hash state; its bytes do not require a field-element canonicality assumption. Seven round1 WideExact entries are canonical through the previously checked actual echeck/strict-codec transfer chain.

The earlier unbound-root compatibility theorem remains unchanged. Its weaker `isSome` conclusion alone would not identify the decoded root; the stronger Bound theorem exports that identity explicitly. This distinction is part of the endpoint, not merely a fact hidden in its proof.

Remaining source composition: identify these actual proof-input root/round1 slices with the actual row30 transcript-message serialization, connect the candidate parser to the admitted release caller, and close the whole accepted-spend theorem. No full100-bit implementation soundness or privacy claim is made here.

Every focused NUC check exited0 under explicit memory/swap caps with zero process swaps. Every axiom report uses only propext, Classical.choice and Quot.sound. Exact source/import/object/revision/command/resource/axiom receipts are retained. No unchanged broad replay was run.

| Target | Wall seconds | Peak RSS KiB | Axiom reports |
|---|---:|---:|---:|
| `AspisR1ViewParseProbe.ParseShapeRound1Root` | 1.382 | 2648392 | 1 |
| `AspisR1ViewParseProbe.ViewParseRootBinding` | 1.793 | 2640516 | 1 |
| `AspisR1ViewParseProbe.ViewParseRootStrictSecond` | 1.677 | 4101540 | 3 |
| `AspisR1ViewParseProbe.ViewParseRootStrictSecondBound` | 1.756 | 4101008 | 3 |
