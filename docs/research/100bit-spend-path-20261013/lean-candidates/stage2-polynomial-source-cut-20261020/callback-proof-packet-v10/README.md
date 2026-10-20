# Current Wide reverse-Horner callback packet

This packet freezes a narrow source cut and its Lean callback proof. It contains no compiled object files.

The retained Rust source is the frozen `verifier::polynomial` body at revision `c8ea8dd49c81ab970b9dbee8d8b47718f9beb005`, original `crates/aspis-r1-cost-probe/src/verifier.rs` SHA-256 `8a704eea668d04ca173290ca894c7cb0ab1f29abef4fec9bb49fbb36476779ea`, byte span `[12595,12695)`, span SHA-256 `ca19094cb9ea4f1b293554b0ec68d055ccc1dd71488f16f6e5f5043c631e48a7`. Its exact shape is `(0..7).rev().fold(E::ZERO, |a, i| a.mul(x).add(field(bytes, i)))`.

Aeneas translated this isolated source cut successfully. The recorded LLBC hash is `5a403315f2a9eb02d5a5f7414641082ac6a4024a18c6468eaef8d95027216500`; generated Funs hash is `2c7ba8935b7365531286ea1c4c8d1db9c55b590ac748ad571bb4e08d`. Generated callback order is multiply, coefficient lookup, then add. The companion external template declares `Rev.fold` and `weights.field`; it is preserved only as diagnostic provenance and is not imported by the Lean proof. The generated cut’s local add/mul bodies were unreachable stubs, so its generated Funs does not certify arithmetic behavior.

`CurrentWidePolynomialHornerListV10.lean` instead proves the callback recurrence over the exact current `WideExact` implementation. A successful lookup-aware run over indices `[6,5,4,3,2,1,0]` yields a `List.Forall₂` trace tying each coefficient to its requested lookup, coefficient canonicality, canonical output, and the decoded Horner value. The step proof uses the pinned `CurrentWideProduct.wide_mul_success` and `wide_add_success` owners; the exact current zero constructor is separately proved canonical and decodes to zero. Printed axioms are only `[propext, Classical.choice, Quot.sound]`.

The current source cut and recurrence theorem do not prove that Aeneas `Rev.fold` is equal to this list recurrence, do not instantiate `weights.field` with the concrete decoder lookup, and do not close the surrounding `finish_relation` caller. Those interfaces remain explicit. In particular, the generated external template is not evidence for those facts.

## Lean attempt

The successful target is `CurrentWidePolynomialHornerListV10`, compiled on the pinned NUC with the accepted current-wide proof roots. Exact source/object pins, direct import pin, runner command, preflight, admission, reservation, time log, Lean output, and full ordered `LEAN_PATH` are in `evidence/lean-v10/`. `CurrentWideProduct` is imported at object SHA-256 `f010a1f6ecd992a9a3e4a2661a26b45bdfcfb6e570b8f873f184eb591bb24346`; its source and receipt are included/referenced in this packet, with the remaining current-wide owner closure retained in the repository evidence directory `evidence/session-b-current-fold-arithmetic-20261020/`.

The source-cut Charon/Aeneas command receipts and tool hashes are under `evidence/charon/` and `evidence/aeneas/`. The measured proof attempt took 2.206 s, process RSS 4,016,268 KiB, cgroup memory peak 382,042,112 bytes, cgroup swap peak 0; the scope was `MemoryHigh=1GiB`, `MemoryMax=2GiB`, `MemorySwapMax=0`. The fresh admission passed with 26.375 GiB finite reservations, 8.853 GiB charged uncapped working memory, and the required 8 GiB OS growth reserve.
