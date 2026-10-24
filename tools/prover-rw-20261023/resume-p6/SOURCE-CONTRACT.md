# Concrete prospective contract: statement, not an established theorem

The complete source and carriers are `proof/selected.rs`, shared identically
by `compact/proof/selected.rs`. No source theorem, premise or trust assumption
was removed. Public statement before and after:
`generate_for_mask_nonce(nonce:[u8;32]) -> Result<StateOnlyAttemptSecrets,StateOnlyAttemptEntropyError>`.
Private selected statement before FactoryState and after the job-prefix rename:
`Draw { request:Request{mask_nonce:[u8;32],retry:usize}, bytes:Zeroizing<[u8;64]>, outcome:Result<(),getrandom::Error> } -> (Control,Result<Option<StateOnlyAttemptSecrets>,StateOnlyAttemptEntropyError>)`.
`Control = More(Request) | Done`; `Secrets` has nonce32, field Zeroizing32,
leaf Zeroizing32; `Error = Os(getrandom::Error) | RepeatedZeroBlock`. There is
no hidden output equivalence field. Native source has no World parameter.

Quantifiers: every nonce32 (including zero for the local resume contract),
every entry r in0..15, every initialized64 postbuffer b, and every primitive
Ok or Err(e), where e ranges over ALL NonZeroI32 representations valid on the
pinned host x86_64 Linux. The constructor is representation-total, not a claim
that an OS returns every such value. Let F=b[0..32], L=b[32..64], and A be
`some byte of F !=0 && some byte of L !=0`.

| Primitive/path | Control/result | Normal destructor observation before delivery |
| --- | --- | --- |
| Err(e) | Done, Err(Os(e)) | bytes64: b -> zero64; no32 owners constructed |
| Ok, A | Done, Ok(Some(owner{nonce,F,L})) | bytes64: b -> zero64; returned32 owners still LIVE |
| Ok, !A, r<15 | More(Request{nonce,r+1}), Ok(None) | leaf32 L -> zero32, field32 F -> zero32, bytes64 b -> zero64 |
| Ok, !A, r=15 | Done, Err(RepeatedZeroBlock) | same leaf32,field32,64 sequence |

Each normal destructor is invoked once per actual owner in the relevant scope;
its pre/post snapshots must come from that invocation's live valid storage.
On rejection retry increment is before those lexical destructors in actual
source. On success later explicit returned-owner disposal is a DISTINCT phase:
field32 then leaf32. Snapshot equality cannot by itself identify equal-payload
owners; a source-role/move/lifetime argument remains necessary. No double-drop,
child-pointer retention, read-after-drop or padding assumption is permitted.

`Request::draw` must execute literal fill exactly once on freshzero64 before
constructing Draw with its actual outcome/bytes. The Kani harness checks this
under the sole primitive boundary stub, including arbitrary ledger-after held
outside Result. That ledger is NOT the OS world. Native transition W -> W'
and an experiment/error-observation transport have no source producer here.
The required relation must keep every fill entry/outcome/postbuffer and ordered
world transition including Err, and carry the resulting history to the outer8
adaptive public policy and durable ledger. No output/acceptance equality is a
substitute. Literal contextual successful64 E1 and L1/L2/L3 remain explicit.

Start guards zero nonce before draw and initializes r=0 otherwise. A whole
controller proof must establish at every actual entry that r equals the number
of earlier rejected draws, those draws have the same nonce, r<16, and remaining
rank is16-r. The local modulo16 harness does not prove this reachability invariant.
No finite16 or Lean controller composition is justified until the concrete
source/P6 relation, instrumentation admissibility/erasure and actual entry
producer are proved. No native, privacy or deployed target is established.
