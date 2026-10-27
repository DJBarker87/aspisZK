# LPn ValidatedRecord::decode_k — CLOSED

CLOSED on the adopted caller domain: N=1/28/29, all offset values (including
usize overflow), every row byte, every well-framed input of length5..3717,
arbitrary bytes, both row/length errors and exact first NonCanonical index.
No canonicality hypothesis on input bytes. The actual callers' maximum payload
is3712 bytes and116 values. No headline premise removed.

## Native, source and model

Frozen4bb3b3f51e16b4525f1d10336e2b0bcbbd775387, r1_wire.rs:117–172,
Prefix::record/validated_record at338–352. Native code: row gate; checked32*off,
32*N and sum; payload[5..] range; ZERO array; enumerate32-byte windows; decode
low16; write SAME value slot; immediate error at off+value; return owned array.
No oracle/hash/allocation or user callback. High16 are intentionally unread by
this leaf; prior validation belongs to genuine tokens and is not assumed to
make malformed low16 inputs disappear.

LPn_Kit_DecodeModels copies the inherited XRk_DecodeModels body without semantic
changes. LPn_TRANSFORM.json pins exact original/copied hashes and import/name
mapping. The carrier is the SAME LPl_Kit_Release type already used by completed
LPl leaves; no candidate, model body, enum tag or existing proof module edited.
The existing LPa decode laws and byte-bound/word proofs are imported through
permitted name/import copies; no old theorem is re-proved.

| Stage | Evidence | Scope |
|---|---|---|
| Guard and range | K005 | Actual source scalar sequence on all row/usize offsets, N=1/28/29, all bounded framing lengths. Exact overflow/error precedence and selected slice. |
| Iterator/carrier | K003 | SAME payload/slice pointers,32-byte window, index/count/exhaustion for every fitting range and reached cursor; selected index<116. |
| Decoder/Result | K006 | Every32-byte chunk, row and bounded off+i; exact four natural limb values, canonical flag and NonCanonical row/index. |
| Native typed write | K009, strengthening K007 | Actual native N1 call then assignment into arbitrary typed QM31 pre-state. Every u32 representation allowed; no canonicality restriction retained. Exact written cell and both frames, no write on rejection. |
| Token getter | K008 | Actual Prefix getter's row rejection and SAME row/reference/length return; distinguishable pointer table entries. Literal getter association preserves original slice carrier, not merely equal lengths. |
| Native non-vacuity | K010 | ZERO succeeds even with arbitrary unread high16; low word P rejects at exact index; invalid-row priority and usize overflow reject. |
| Byte association | L054 | LPn.Decode.word_value/step_good; natural little-endian polynomial and exact four model words/acceptance flag. Existing generic bounds reused. |
| Output/frame induction | L057 | LPn.Decode.Trace/Write, invariant/output/unique/total. Coordinate maps selected global array cell to native before/write/after cell0/1/2. write_of_local instantiates the local relation for all29 writes (and1/28), no native row enumeration. |
| Full model Results | L059 | LPn.Decode.native_success/native_error; source scalar Ready cases; exact returned array and first-error index; row/arithmetic/range errors. Ready is the actual guard's branch condition, not a caller assumption; K005 decides it for every input. |
| Bounded error and provenance | L060 | error_bound derives off+i<116 and scalar-port safety from SAME Ready/range/scan; token_unique identifies SAME row/framed carrier. |

## Complete composition and provenance

K003 identifies the exact bytes K006 decodes; L054 ports their four values and
flag to DecodeModel.step. K009 proves native write/frame observations for an
arbitrary pre-state. L057 transports the three-cell observation to a global
array cell and inducts over its index: previously decoded prefix remains;
current cell is set; future cells remain ZERO until reached. At exhaustion all
N cells are identified with the SAME ordered model values. LPl.Scan.first_error
supplies the exact first rejected index; no suffix executes after rejection.
L059 joins both local traces to the full outer Result, including owned array
carrier identity. L060 proves the error-index scalar cannot panic on the
adopted size bound. Local native gates construct these traces in source order;
no final whole-output equality or independently accepted execution is assumed.

A genuine token comes from the SAME Prefix::validated_record row and its
stored slice, not a separately chosen byte input. K008/L060 cover that local
getter association. Upstream Prefix::parse checks tag/exact row size, and the
completed LPl validation leaf checks every field; those upstream obligations
and enclosing caller installation remain their own cone. The decode bridge
itself works for all bytes in any bounded framing length≥5. A fabricated
shorter token would panic at payload() and is outside genuine-token callers;
this does not hide a low-limb rejection or strengthen an actual caller.

K009 removes even the canonical pre-state restriction from K007, so no
canonicality invariant is needed to consume its frames. Local source-to-model
observation transport uses the same compiler/platform/library/P6 boundary as
LPk/LPl; Lean does not elaborate Rust. No new library/frame trust is added.

## Validation and limits

K004's32-byte array assertion failed a builtin memcmp unwind10 check; K006
replaced that assertion with four scalar comparisons at unchanged limits.
L052/L053 all_congr binder errors; L055 lexer spacing error; L056 coordinate
case proof errors; L058 opaque-predicate rewriting/range simp errors are retained,
never credited. Passing source replacements L054/L057/L059/L060 carry printed
standard-only axioms. All old copied laws also print their inherited audits.
No timed-out/memory-killed shape rerun, cap increase, or whole-buffer loop.

No stubs or multiplication. Every native run has fresh frozen offline graph,
unchanged frozen lock, exact patch/source/tool/argv/revision/exit/wall/RSS/swap
receipts. Every proof has -M7000 and printed axioms. Serial6G/8G/swap0/tasks64
scopes; shared launchers unchanged. Only this prefix/evidence changed.
No headline input/trust item/metric/game/bound changes; AspisR1.RPx_Deployed.deployed
unchanged, L154 statement parameter, frozen3/RuntimePersistence/narrowed D188
retained. S2/100-bit target not established. No full release replay or source-to-
ELF/installation claim. Shipped sources unchanged; ELF pins inherited, no rebuild
trigger. No push, merge, session A/candidate edit or wallet/key cleanup.
