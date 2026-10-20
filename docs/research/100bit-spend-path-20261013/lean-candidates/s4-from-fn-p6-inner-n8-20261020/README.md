# P6 N=8 generated callback consumer

The checked consumer proves that a successful P6-model `from_fn` at length 8, using the emitted `fast_dots.four_dots.closure` callback, exposes all eight ordered array reads and reducer calls. It returns `values.val = [m0, …, m7]`, with each `mi` tied to the successful `m31ReduceU64` call on the corresponding `limbs[i]`; it also derives callback closure preservation and the cursor progression from the trace. The theorem takes one successful modeled array call, not eight independent callback-success premises.

`S4FromFnP6InnerN8ConcreteV2.lean` is checked at source SHA `06f4bc3f7e567100ca707275901ecae97a0b845c6aae714c5df3b2807141285e`, object SHA `614bce450384e017043a1c6a6194e55587987ea45e87b7ddd3bb390d3b81f65e`. Its receipt and complete import preflight are in `../../evidence/s4-from-fn-p6-inner-n8-20261020/receipts/S4FromFnP6InnerN8ConcreteV2.replay-v1.*`. The compile exited 0 in 2.037 seconds, with peak RSS 2,273,263,616 bytes and swap 0. The axiom audit reports only `propext`, `Classical.choice`, and `Quot.sound`.

The N=8 generic success trace owner is checked at source SHA `ec38f3e96104d611f19bfd7db7873716c7f7d1cbd993558542c61fc262e1d725`, object SHA `d4c0e3010fb4a93fca3febcb87297e556be92cbbd3db032f666adb1f761a41d0`; its producer receipt is in the evidence packet. The failed consumer attempts are retained in that packet's `diagnostics/` directory and are not selected.

The P6 operational model remains an explicit boundary for Rust `core::array::from_fn`. This theorem does not establish universal Rust standard-library correspondence or close the whole `four_dots` caller. No Lean binaries are included in the evidence packet.

The selected receipts are the one-time provenance replays at captured launch revision d93756b49. Original hard-coded revision records are retained as superseded diagnostics; no unchanged replay is needed again.
