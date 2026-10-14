# Commitment root frame source pins

Base revision: `eac8ca7d792be9438200ec839b30102a5204881d`. These pins identify the requested Rust literal locations. They do not establish a complete Lean/Rust semantic correspondence.

| Source | Lines | Relevant literal/operation | SHA-256 |
|---|---:|---|---|
| `crates/aspis-r1-cost-probe/src/r1_wire.rs` | 39–48 | `row_shape(2) = Some((1, 32))`; row 2 has tag `1`, payload length 32. | `73f4b49dfae90be8a5cafd9d69eaf9ed06a01009f3daabc5627b42e6cf31c996` |
| `crates/aspis-r1-cost-probe/src/r1_wire.rs` | 189–203 | `sample_block_validated` hashes `[state, [0, 0xa0 + row], framed]`; for row 2 the two-byte label is `[0, 0xa2]`. | same as above |
| `crates/aspis-r1-cost-probe/src/host_semantic.rs` | 102–103 | C2 root is committed, then `scalar(2, &c2_root, ...)` feeds the row-2 challenge. | `113a367ae1e01d8fbd808ce3756b87040fd31ab359d94bad50b7c55c89c284bf` |
| `crates/aspis-r1-cost-probe/src/transcript.rs` | 14–20 | `absorb(row,payload)` hashes state, `[0, 0xa0+row]`, u32 payload length and payload; `block` then squeezes and advances. This is the generic row-30 absorb path. | `c91ffe824a55ff62659e8a194d2ea201032383e4e11e5f60625404a30c691ef6` |
| `crates/aspis-r1-cost-probe/src/prover.rs` | 223–226 | Folded root is serialized and concatenated with `c1bytes`; the resulting payload is passed to `t.scalar(30, ...)`. | `a7e20e5eb2fb706f2bdb51371466d4ee02c6fcabc67a427495a3b9276d9495fd` |
| `crates/aspis-r1-cost-probe/src/verifier.rs` | 92–95 | Verifier concatenates the 32-byte folded root with `round1`, reserves `32+224`, and passes it to `t.scalar(30, ...)`. | `2cab573be46ca69b5d82837e5221a9a499d3b6dc1f89b801e388b4e8b1fe01cd` |

The Lean frame definitions in `CommitmentRootFrames.lean` are literal target-reader frames: C2 prefix `bytes state ++ [0,0xa2,1,32,0,0,0]`; folded prefix `bytes state ++ [0,0xbe,0,1,0,0]` followed by a root and a 224-byte tail. This note pins the Rust sites requested; it does not prove complete semantic or source correspondence.
