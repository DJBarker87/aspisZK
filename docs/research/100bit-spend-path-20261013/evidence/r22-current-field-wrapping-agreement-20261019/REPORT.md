# R22: checked and wrapping field-kernel agreement

Three focused modules now prove exact equality between the extracted checked field kernels and their wrapping-primitive expressions on the stated domains. Addition and subtraction require canonical M31 inputs; the U64 reducer and widening M31 multiplication require no canonical-input premise. The output is canonical in each case. This is progress on the new release-arithmetic gap R22; it is not a whole-verifier refinement or a change to the release compiler settings.

`CheckedWrappingScalarAgreement` proves that successful actual Aeneas unsigned add/sub/mul return exactly the corresponding wrapping result and imply the required no-overflow bound. Successful checked execution alone has the wrong direction for R22; the next modules establish total checked execution on their domains, using the existing current-source range and modular-arithmetic proofs.

`R22CanonicalM31AddSub` proves the actual emitted current M31 add/sub are total and equal their wrapping bodies on canonical inputs, and preserve canonicality. `R22CurrentReducerMul` proves both reducer folds and the entire actual U64 reducer are total and equal the wrapping body on every stored U64; the actual widening product similarly agrees on every pair of stored U32 values. Existing symbolic reducer and M31 proofs supply the modular arithmetic and canonicality facts. No large recurrence or concrete field reduction was introduced.

| Target | Exit | Wall | Peak process RSS KiB | Cgroup peak bytes | Swap bytes |
| --- | --- | --- | --- | --- | --- |
| Primitive scalar bridge | 0 | 2.611 s | 2,619,924 | 320,770,048 | 0 |
| Canonical current M31 add/sub | 0 | 2.107 s | 2,632,340 | 317,652,992 | 0 |
| Current reducer and widening multiply | 0 | 1.705 s | 2,629,572 | 304,103,424 | 0 |

All 13 printed theorem reports contain only `propext`, `Classical.choice`, `Quot.sound`. The exact source revision labels, compiler/source/object/import hashes, ordered import paths, commands, scope admissions and reservations, GNU-time output and receipts are retained in the immutable archive. All 99 payload hashes and the three accepted target sources were checked on publication. Each focused NUC job used MemoryHigh=512 MiB, MemoryMax=1 GiB, MemorySwapMax=0; no OOM or swap occurred. No full manifest replay was started.

Archive SHA256: `d7a73b216f73ef575076c37ab2069b94823c617dcc5949c5d16c0db3e3a74048`.
Readable sources are under `lean-candidates/r22-current-field-wrapping-20261019`.

Remaining R22 work includes the extension-field/fast-pairing kernels, source input canonicality and preservation throughout every admitted stage-1/stage-2 path, loop/index/control arithmetic and an end-to-end release-acceptance-to-model-acceptance theorem. This packet makes no Merkle acceptance, checkpoint hashing, hash-call-count or deployed artifact claim. The commitment-layer hold remains respected.

Failed predecessor snapshots and receipts are retained. Reducer/mul v1 and v2 failed during import loading because copied cache sidecars/IR were missing; v3 exposed a local implicit-width inference error in the product bound. Copying the exact owner sidecars and using the existing explicit product-bound proof fixed those issues; v4 passed. These were not memory-pressure failures and no resource cap was raised.
