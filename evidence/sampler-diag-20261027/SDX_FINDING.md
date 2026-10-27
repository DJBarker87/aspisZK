# Sampler diagnostic (in progress)

No premise removed. S2/A2 and the 100-bit target remain open.

## Q1 Native
Frozen source revision `4bb3b3f51e16b4525f1d10336e2b0bcbbd775387`, scratch-only cfg(test) wrapper, `cargo test --release --locked --offline -j4`. SDX_R003 passed.

| Block | Digits | Quotient |
|---|---|---|
| P | [0,1,0,0,0,0,0,0] | 0 |
| zero | [0,0,0,0,0,0,0,0] | 0 |
| P+1 | [1,1,0,0,0,0,0,0] | 0 |
| 32 ff | [255,2048,7168,14336,17920,14336,7168,2048] | 256 |

Graph validated against frozen Cargo.lock before each test launch; offline and lock hash unchanged (SDX_graph.json, SDX_lock.json). R001 failed before compilation because c3 path source was not yet copied; R002 failed on scratch println without std qualification; R003 corrects that wrapper. No timeout or memory kill.

## Q2 Emitted
Pending dependency/provenance identification and concrete proofs.

## Q3 Location
The XRn loop discards division at Funs:3623. Raw emission and external restoration must be distinguished.

## Q4 Scope
Pending full emitted call-site inventory.
