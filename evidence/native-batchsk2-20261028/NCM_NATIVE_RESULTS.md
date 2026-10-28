# Native helper results

25 actual frozen-helper shapes PASS, with 25 matched intended assertion FAIL controls.
All 50 runs used pinned cargo-kani0.67.0, optimized profile3, frozen offline
lock/graph validation before launch and unchanged lock afterward. No timeout,
memory kill, increased cap or K-2 quarantine. No SHA or field multiplication
was modeled or unwound. Exact KMX patch sha256:
bcdf749b78eb6143789500d98d64ec3d407b8a17a6d1290c70c822473e8e9a67.

The digest spy is data-only, Copy, containing expected borrowed slices, reply
bytes and scalar mode/offset/negative flag. It contains no function pointer
or Option<fn>. No helper or harness was renamed to change a verdict.
Controls invert the SAME selected property; locations and exactly-one-failure
checks are audited in NCM_NATIVE_AUDIT.json. Kani prints no_std panic failures
as an unreachable/format placeholder; the audit checks the intended source line.

These are helper-level native facts, NOT complete NCE fragment instances.
The actual Rust helpers are called without source-loop clones or whole-buffer
loop replay. Per-byte windows use arbitrary symbolic source arrays and offsets.
The whole same-carrier PC/borrow/cursor/write/log association remains open.
No full fragment is claimed discharged or silently instantiated in either top.

| Shape | PASS | Matched FAIL | Domain |
|---|---|---|---|
| key_read | NCM_K001 | NCM_K002 | arbitrary keys[16], i<16; actual scalar accessor only |
| occupied_geometry | NCM_K003 | NCM_K004 | actual occupied helper, symbolic source arrays, index bound, arbitrary offset in selected part; concrete data observer without function pointer |
| occupied_first | NCM_K005 | NCM_K006 | actual occupied helper, symbolic source arrays, index bound, arbitrary offset in selected part; concrete data observer without function pointer |
| occupied_second | NCM_K007 | NCM_K008 | actual occupied helper, symbolic source arrays, index bound, arbitrary offset in selected part; concrete data observer without function pointer |
| occupied_reply | NCM_K009 | NCM_K010 | actual occupied helper, symbolic source arrays, index bound, arbitrary offset in selected part; concrete data observer without function pointer |
| left_geometry | NCM_K011 | NCM_K012 | actual left helper, symbolic source arrays, index bound, arbitrary offset in selected part; concrete data observer without function pointer |
| left_first | NCM_K013 | NCM_K014 | actual left helper, symbolic source arrays, index bound, arbitrary offset in selected part; concrete data observer without function pointer |
| left_second | NCM_K015 | NCM_K016 | actual left helper, symbolic source arrays, index bound, arbitrary offset in selected part; concrete data observer without function pointer |
| left_reply | NCM_K017 | NCM_K018 | actual left helper, symbolic source arrays, index bound, arbitrary offset in selected part; concrete data observer without function pointer |
| right_geometry | NCM_K019 | NCM_K020 | actual right helper, symbolic source arrays, index bound, arbitrary offset in selected part; concrete data observer without function pointer |
| right_first | NCM_K021 | NCM_K022 | actual right helper, symbolic source arrays, index bound, arbitrary offset in selected part; concrete data observer without function pointer |
| right_second | NCM_K023 | NCM_K024 | actual right helper, symbolic source arrays, index bound, arbitrary offset in selected part; concrete data observer without function pointer |
| right_reply | NCM_K025 | NCM_K026 | actual right helper, symbolic source arrays, index bound, arbitrary offset in selected part; concrete data observer without function pointer |
| leaf0_geometry | NCM_K027 | NCM_K028 | actual leaf0 helper, symbolic source arrays, index bound, arbitrary offset in selected part; concrete data observer without function pointer |
| leaf0_first | NCM_K029 | NCM_K030 | actual leaf0 helper, symbolic source arrays, index bound, arbitrary offset in selected part; concrete data observer without function pointer |
| leaf0_second | NCM_K031 | NCM_K032 | actual leaf0 helper, symbolic source arrays, index bound, arbitrary offset in selected part; concrete data observer without function pointer |
| leaf0_reply | NCM_K033 | NCM_K034 | actual leaf0 helper, symbolic source arrays, index bound, arbitrary offset in selected part; concrete data observer without function pointer |
| leaf1_geometry | NCM_K035 | NCM_K036 | actual leaf1 helper, symbolic source arrays, index bound, arbitrary offset in selected part; concrete data observer without function pointer |
| leaf1_first | NCM_K037 | NCM_K038 | actual leaf1 helper, symbolic source arrays, index bound, arbitrary offset in selected part; concrete data observer without function pointer |
| leaf1_second | NCM_K039 | NCM_K040 | actual leaf1 helper, symbolic source arrays, index bound, arbitrary offset in selected part; concrete data observer without function pointer |
| leaf1_reply | NCM_K041 | NCM_K042 | actual leaf1 helper, symbolic source arrays, index bound, arbitrary offset in selected part; concrete data observer without function pointer |
| leaf2_geometry | NCM_K043 | NCM_K044 | actual leaf2 helper, symbolic source arrays, index bound, arbitrary offset in selected part; concrete data observer without function pointer |
| leaf2_first | NCM_K045 | NCM_K046 | actual leaf2 helper, symbolic source arrays, index bound, arbitrary offset in selected part; concrete data observer without function pointer |
| leaf2_second | NCM_K047 | NCM_K048 | actual leaf2 helper, symbolic source arrays, index bound, arbitrary offset in selected part; concrete data observer without function pointer |
| leaf2_reply | NCM_K049 | NCM_K050 | actual leaf2 helper, symbolic source arrays, index bound, arbitrary offset in selected part; concrete data observer without function pointer |

Native peak RSS max: 2261016KiB; maximum wall 25.65462935192045s; swaps0 throughout. Exact targets, revisions, source hashes, graph hashes, limits and per-run metrics are in NCM_K001..050 receipts.

The resolved graph has441 packages from the444-package frozen lock. The
three omitted optional packages are aspis-r1-cert-build, aspis-r1-cert-check
and aspis-z4b-probe; no new package or unpinned dependency edge is admitted.
Every run has the same metadata hash. No historical LPb native stage is reused
or given credit here. CFG-only scratch changes are committed solely as
NCM_native.patch; exact KMX patch is referenced at its original evidence path.

Lean value-law composition: NCM_KMXWindows proves adjacent-window composition,
disjoint destination commutation and the window/frame characterization over
KMX_CopyMeaning.loop_spec. NCM_DigestWindows transports arbitrary finite-byte
windows to exact lists and argument/reply pairs. NCM_PartsWindows lifts this
to the existing nested physical Parts type; NCM_ReadWindows binds one such
call to the exact chronological event appended to the SAME prior log.
These are conditional Lean joins; Kani verdicts are not inserted as axioms.
The native-to-Aeneas call-site/event association is still OPEN.
