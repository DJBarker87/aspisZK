# Narrow ordinary decoder cache reuse

The authorized metadata-only append completed with exit 0 and
`ORDINARY_DECODER_CACHE_APPEND_PASS=2`. No compiler ran during this operation.

Source parent is `15700387af1d52af4b7ddff8de92541ec2891ff2`; borrowed V7 is
`26a9cd4718aae9f9de7ef1c3394fb74a229085d5`. The existing higher-Y overlay and
runner retain their creation pin `289d7356c78a4cd493fe61a54f9548f2a0c11298`.
Access used Tailscale `dombarker@100.108.41.90`; `nuc.local` was only the pinned
SSH host-key alias, not the network route.

Only `AspisFormal.K1.V7Tag73EightRetryDecoderBridge` was appended:

- Source SHA-256 `027dc6b1a91fe9b21bdd7db6929fb70da4aa204745e8cc39bbc4cd5fb48673e4`.
- Olean SHA-256 `1039d5af8c2991fd6d16c3d5fa7a86d8804c29abfaa79c9084300a867c47c94d`.
- Retained local Lean 4.32 trace SHA-256 `9d7760d12b7eec78692f7e120e3bff0d4be26bad814d8869712a0408301ca1d4`.

The source matches the borrowed git blob. The local monolithic olean records
the pinned Lean version/commit; its retained trace has two standard-only axiom
audits and no errors. These are reused proofs, not new theorem credit. The
new focused Prefix leaf is the subsequent native import compatibility check.

The base manifest grew from 798 to 800 entries without replacing any entry.
Its new SHA-256 is
`001f1020072a53448a455d85eeb1568a1c8cb09125bc025b5d4188d230882fec`.
All 865 artifacts of the frozen RawMass v2 run and all 34 registered green
targets were byte-verified before and after; its manifest and green-state
bytes stayed unchanged. The base manifest was atomically replaced, not written
through an inherited hardlink. No native output variant was substituted.

The three exact boundary pairs are EightRetrySamplerLaw, SamplerDecoderExact
and SamplerExactValue. The last was already pinned and needed no append. This
does not import the full FlatRouting/semantic closure or borrow drifted main
sources. The complete operation receipt, before/after manifests and trace are
retained under `ordinary-decoder-cache-*`.

Read-only verification:

```sh
python3 docs/research/v8-no-work-100-20260907/experiments/audit_ordinary_decoder_cache.py
```

Cache reuse supplies no sampler law by itself. The actual one-call block law,
nested tape routing, adaptive transcript coupling and global soundness remain
separate proof obligations with their own receipts.
