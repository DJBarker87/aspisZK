# Selected raw-round canonicality evidence

This focused Lean target proves that successful decoding under the selected bounded message codec re-encodes each message to its original bytes, then applies the generic raw-round canonicality theorem to obtain exact raw-record-list reconstruction. The result is codec/list plumbing only; it does not establish Rust refinement or protocol acceptance.

Attempt `R1SelectedRawCanonical-a` exited 0 in 1.44 s, with 3,563,168 KiB peak RSS and zero swap under the 4G/6G/0 cgroup. Its two public axiom reports are `[propext]` for `dec_sound` and `[propext, Classical.choice, Quot.sound]` for `encode_of_decode`. The archive contains the target and both direct imports. Exact source, object, runner, and receipt pins are in `source-manifest.json`.
