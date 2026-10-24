# One-draw relation and composition boundary

For the candidate `proof-cut/selected.rs::one_draw`, Kani056 checks:

- Every entry r in0..15 and every public nonce32 (including zero).
- Exactly one primitive call, with initialized zero64 before it; arbitrary
  postbuffer64 on either Ok or Err. This includes partial-write final states.
- Custom-u16 getrandom errors only, passed unchanged through actual From and ?.
- Ok cut-result Some iff both32 halves are nonzero; both moved Zeroizing32
  owners contain exactly those halves, and nonce is unchanged; retry stays r.
- Ok cut-result None iff either half is zero; retry=r+1<=16, with retry=16 iff
  entry=15. Its remaining-count measure16-retry decreases by exactly1.
- The arbitrary ghost provider u64 advances to the chosen value on every
  primitive result, including Err. This is not actual OS hidden-state transport.

Error and rejection are distinct. No cut result is called factory exhaustion.
No success, nonzero draw, independence, freshness or uniformity is assumed.
The symbolic output index is any u8 modulo32, hence covers all32 positions.
Kani treats the fence sequentially; all pointer/safety/unwinding checks remain
on. Unsupported constructs are globally warned and would fail if reachable.

The factory source guard rejects nonce zero before entering the body. The
source increments retry only on the same rejection path. If the one-draw
relation were connected semantically to that actual body/caller, the ranking
16-r and initial r=0 would justify at most16 draws, with the16th rejection
exhausting the controller. This is the finite composition argument to establish,
NOT an accepted theorem: Kani056 proves the cut, not that source association.
Kani055 tried actual-loop invariant establishment/preservation and the complete
normal Result relation, but timed out. It is not an accepted composition proof.

`cut-source.py --check` demonstrates syntactic factoring: every copied body
byte is unchanged except the success return wrapper. The new method signature,
entry retry, removed nonce guard/while, and rejection-result wrapper are recorded
in cut-source-map.json. This does not mechanize Rust/MIR semantic equivalence.
No hand-written loop theorem or desired-output premise fills that gap.

Actual zeroize1.8.1 Drop is never stubbed. The cut retains the lexical scope:
Err drops bytes64; rejection exits with leaf32/field32/bytes64 owned locals;
success moves both32 owners out and drops bytes64. The actual returned owner
is dropped in the harness. These are source execution/ownership observations,
not verified dynamic event counts/order, post-destruction storage observations,
unwind/abort coverage or hardware erasure. The reused native-owned-drop leaf
checks and retained-storage lifetime argument do not supply whole-caller
provenance or instrumentation erasure/admissibility.

No existing theorem statement or premise is changed. New cut statement:
`one_draw : (nonce32, r) -> Result<(r', Option<Secrets>), Error>`;
actual statement remains `generate_for_mask_nonce : nonce32 -> Result<Secrets, Error>`.
The former is a separate component with different input/output carriers; it is
not premise removal from the latter. Neither deployed target is established.
