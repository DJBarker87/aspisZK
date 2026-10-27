# LPl verifier::echeck native P6 bridge

CLOSED on all adopted release scanner domains: every input of length at most
2272 bytes and both
values of k, including every rejected prefix. No headline premise removed.

Porting the SAME native slice bytes by their U8 natural values and the native
Result's Ok/Parse tags gives `LPl_Kit_Release.verifier.echeck bs k =
ok (if nativeAccepted then .Ok () else .Err .Parse)`. The model is the name-only
copy of the inherited XRk opaque-leaf model, not a changed decoder or protocol.
Its exact source/nominal transport is recorded in LPl_transform.json. This is
an opaque-leaf P6 bridge under narrowed D188, not installation into the headline.

The exported Lean theorem is `LPl.Echeck.native_result`. Its explicit local
`Trace` is constructed by the universal native gates and verbatim source
association below. It has no whole-function equality field, arbitrary native
accepted run, independent input, canonicality assumption or supplied model
result. As in LPk, Rust/Kani/Lean association is part of the hybrid P6 argument;
Lean does not itself elaborate Rust. The theorem is generic in slice length;
the native full-carrier certificate K008 covers every length0..2272, including
all tails. K009 checks the actual adopted caller constants:32,224,2272,128.
Audit-only eight_way callers are outside this adopted release closure.

## Source and model pins

Frozen Rust revision: 4bb3b3f51e16b4525f1d10336e2b0bcbbd775387.
`verifier.rs:39` reads successive `chunks_exact(32)`, decodes WideExact,
returns Parse on decoder rejection or nonzero high half when k, then returns
Ok at iterator exhaustion. It has no digest/oracle operations or visible
mutable output. LPl_SOURCE.json pins that body and field decoders to frozen
bytes; inherited cfg instrumentation and the LPl include are scratch-only.

LPl_Kit_FunsExternal copies the inherited XRk_FunsExternal decoder predicate
and echeck definition exactly modulo module/declaration prefixes. All21 reused
modules are reconstructed byte-for-byte by `LPl_transform.py --check`.
Types additionally uses the already selected ImportUnionNamedDiscriminant
adapter, qualifying only generated instance names; no enum tag/type/body edit.
LPl_Coimport tests the prior `instDiscriminantErrorIsize` collision context.
No old theorem is silently reassigned to a different nominal type.

## Complete association

| Stage | Evidence | Scope |
|---|---|---|
| Native decoder | K001 | Every32-byte chunk, both k; canonicality of all8 words and conditional high-half zero equal the nonwrapping u64 base256 predicate. No assumptions/stubs. |
| Immutable iterator | K002; inherited LPh K009/K010 | Every index0..29 of arbitrary928 bytes; K008 additionally covers every index
of every length0..2272: exact SAME backing pointer,32-byte window, remaining count, next-front pointer and empty terminal. Prior-good/error cases inherited, independently joined by K003. |
| Native local Result | K003 | Every32-byte chunk, both k, arbitrary prior-good state; source echeck Result is exactly the local polynomial predicate, preserving Parse. No decoder/multiplication stub. |
| Byte-value join | L023 `word_eq_le32/chunk_eq/window` | Explicit little-endian base256 polynomial equals model foldr on all byte lists; exact pointer-selected window becomes the model's SAME drop/take window. |
| Cursor/early exit | L024 `read_eq/read_size/advance/trace_result` | Pointer displacement32*i, remaining count, read width, terminal and both local Results; induction on the source-shaped execution, no whole-output premise. |
| Model induction | inherited LPg29-stage and LPa fold laws; L026 `run_all/run_loop/native_result` | Source cursor order joins the model's complete chunk fold and full outer Result, including early rejection. All29 windows included. |
| Tail | inherited LPc K013–K016 and `LPl_C.Echeck.append_tail/count_with_tail` | Native0..63 tail gates and model count/window law retained unchanged; K008 also checks every tail and its exact pointer for lengths0..2272. |
| Uniqueness | L026 `unique` | Two compatible traces for the SAME input/index/k have the SAME result. |
| Non-vacuity | K004; L027 | Native zero success, canonical nonzero-high rejection only when k, P rejection and empty success. Lean total trace existence for every input, zero canonical chunk, rejected chunk and empty Result. No accepted-only precondition. |

For immutable chunks_exact, native K002's pointer/count facts identify the
very bytes decoded by K001/K003; no output allocation, borrow writeback or
mutable callback restoration is involved. `Trace.next` retains these pointer,
index and count transitions; `Trace.reject` terminates immediately. The source
has no other branches or returned state. Kani checks UB, bounds and arithmetic
obligations on the same domains; no source or helper replacement is assumed.

## Stubs, trust and limits

Stub pairing table: none; these gates execute the actual native decoder and
one-chunk echeck. No field multiplication gate, unpaired stub or new trust item.
Compiler/platform/library/P6 association and standard logical axioms retained.
No security game, frozen3, RuntimePersistence, L154 parameter, failure event,
metric or headline quantifier is changed. Headline remains
`AspisR1.RPx_Deployed.deployed`; enclosing S2/100-bit target not established.

L025's rejected parser/tactic error is retained; L026 is the corrected passing
source. Failed sorryAx diagnostic lines are excluded. The byte-prefix copy
script's first namespace-prefix omission was corrected in L002 (L001 retained).
The owned scratch script's binary-file text decoding error occurred before a
prover launch; it was repaired with byte comparison before decoding changed
text. Shared launch/admission/monitor/coherent cache infrastructure unchanged.

Every actual invocation has source revision/hash, dependency/tool pins, exact
command/target/exit/wall/RSS/swap, caps and printed axioms/N/A in its receipt.
All accepted new theorem audits contain only propext/Classical.choice/Quot.sound
or a subset. One scope at a time,6G high/8G max/swap0/tasks64,Lean-M7000;
optimized/offline Kani with fresh frozen-graph validation and unchanged lock.
No cap/timeout raised; no memory kill or unchanged timed-out rerun.

Research crates/programs/Cargo.lock unchanged. No ELF rebuild trigger;
default f8c0ec72621fd5029a97d796c4a3623d0dc44a8e7074122372f9872915d143d4,
devnet63ad3e9cc096dcbb55b3ca7ac7c8e89e6a845796ab5e4f5b7d15db96f3784299,
Pool121f3e29741f510e6dc42d0345fc3c36217600f0be337094855c4a9da2581548
are inherited pins, not newly reproduced. No full manifest replay, source-to-ELF
proof or headline installation claimed. No key cleanup, push or merge.

## Caller-domain correction

The first committed packet established every928-byte input. Source inspection
then found adopted canonical_scan also calls echeck on32,224,2272 and128-byte
segments. Claiming whole release closure from928 alone would be too narrow.
That claim is superseded here. K008 proves immutable iterator transitions for
every length0..2272 and every reached cursor (no field loop); K009 checks the
actual adopted caller constants. Existing arbitrary32-byte decoder/Result gates
and the generic Lean trace/induction apply unchanged. No partial larger field
loop or timed-out shape was rerun. Check_values work paused for this correction.
LPl_DOMAINS.json pins the exact caller source and lengths. No assumption added.
