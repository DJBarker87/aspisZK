# Strict wide byte codec

`StrictWideByteCodec.lean` defines a 32-byte encoding as two adjacent retained 16-byte QM31 encodings. It reuses `decodeQM31LE_encodeQM31LE` and `encodeQM31LE_of_decodeQM31LE` to prove strict decoding roundtrips, successful-decoding half agreement, and encoding recovery. It introduces no canonical-input premise: the retained QM31 decoder rejects any noncanonical limb. This is a byte-model codec only; it makes no source parser correspondence or wide-field arithmetic claim.

The final focused attempt was `strict-wide-codec-c`: exit 0, 1.55s, 3,304,812 KiB peak RSS, zero swap, 4G/6G/swap0. Its three public theorem audits use only `propext`, `Classical.choice`, and `Quot.sound`. Attempts `a` and `b` are retained with exact sources, receipts, and logs; both failed while elaborating the proofs, and the source was revised between attempts.

All attempt snapshot hashes were checked against both the wrapper sidecar and receipt. The runner/environment snapshots and source hashes are recorded in `source-manifest.json`.
