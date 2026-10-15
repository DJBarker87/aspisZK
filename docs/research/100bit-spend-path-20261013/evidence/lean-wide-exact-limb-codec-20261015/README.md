# Wide exact limb codec bridge

`WideExactLimbCodec.lean` defines `pairToExact` by applying the retained canonical `qm31ExactLimbEquiv` to each four-limb half, and `pairExactEquiv` as the product of those equivalences followed by the existing quadratic-product equivalence. It proves equivalence application/injectivity and the literal identity with `R0C.ModuloField.digitsField (Fin.append lo hi)`. The four coordinates are identified via `ZMod.finEquiv` and the existing R599 `tupleFieldEquiv`; the eight digits are split by the already-defined `splitDigits`.

The focused final attempt `wide-exact-limb-f` passed: exit 0, 1.55s, 3,321,884 KiB peak RSS, zero swap, 4G/6G/swap0. All three public theorem audits report only `propext`, `Classical.choice`, and `Quot.sound`. Attempts a–e are retained as failed proof drafts with exact snapshots and diagnostics. The source hash of the cached/imported `R0C.ModuloField` module is recorded in the manifest. This is representation plumbing only, not a Rust parser correspondence or wide-field arithmetic result.

All attempt snapshots match both their wrapper sidecars and receipts.
