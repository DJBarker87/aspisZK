# Rc4 mechanical recount

**S2 OPEN; target not yet established.** Counted actual theorem:
`AspisR1.Rc4_Top.deployed` (022; final audit059), with transparent complete
conclusion `Rc4_Statement.Conclusion`. Before/after kernel statements are
028–034/039, complete source binders in the corresponding committed modules.

Ledger_003–005 method: atomic conjunctive leaves; each universally quantified
law family counted once; shared dictionaries, guards and existential witnesses
remain shared. Classification and correspondence are reviewed judgments;
field extraction, enumeration, row diff and sums are mechanical. No security
percentage, outer-binder count, or logical-solver claim.

| Scope | Rc3 T | Rc3 P | Rc4 T | Rc4 P | Rc4 C |
|---|---:|---:|---:|---:|---:|
| actual antecedent |82|113|82|49|0|
| deployment only |6|13|6|13|0|
| deployment alias |0|4|0|3|0|
| all retained audit rows |88|130|88|65|0|
| deduplicated actual plus non-alias deployment |88|126|88|62|0|

| Scope / owner | T | P | C |
|---|---:|---:|---:|
| actual / lead |0|15|0|
| actual / session A |0|31|0|
| actual / external |82|3|0|
| deployment only / lead |0|12|0|
| deployment only / session A |0|1|0|
| deployment only / external |6|0|0|
| deployment alias / lead |0|3|0|
| deployment alias / session A |0|0|0|
| deployment alias / external |0|0|0|
| deduplicated actual+deployment / lead |0|27|0|
| deduplicated actual+deployment / session A |0|32|0|
| deduplicated actual+deployment / external |88|3|0|
| all retained / lead |0|30|0|
| all retained / session A |0|32|0|
| all retained / external |88|3|0|

Actual independent delta: **64 P**, comprising61 session A +3 lead;
no new T/P/C law family. The security slice excluding the five inherited
bank-protection guards changes82T+108P →82T+44P. The five guards are retained.
All original Rc3 rows have a removed/retained entry in `Rc4_premises.json.diff`.
Every remaining P has owner, exact family, blocker and coverage tag in
`Rc4_REMAINING.md`. Tags identify planned coverage, not imported results.

SAQ's61 verified against the actual root/result, not just its candidate:
N047–N088 query42; N089–N095 geometry canonical7; N096–N104 domain9;
N105–N107 mul/one/inverse3. The42 query leaves are5 basis +9 mulE +9 addE
+5 mulK +4 M31 +1 decoder +1 line +8 canonical line leaves.
`Rc4_Assemble` supplies the sole query owner; `Rc4_Cont` and `Rc4_Literal`
supply the six remaining guard families from those exact source bodies.
The61 leaves are absent as premises of the new result, not repackaged.

TxS's four-row claim verified: N115,L151,L152,L153. **N115 already absent
on Rc3**, hence zero incremental credit; its source-selected SAME saved Vec,
Prepared and model-ten result is retained. L151/L152 are now derived at
`TxS_Carriers.source metadata (typedRows ...)` rather than provided by a
law-bearing Data input. L153 is derived by `Rc4_Model.typed` from raw public
bytes through TxS's checked bound constructor. These3 are model-instance
transport discharges; no native arithmetic result is inferred. Raw-to-typed
surjectivity and reverse transports preserve every old input and full result.
Rc4 additionally exports TxS's full physical saved encoding on the SAME run.

L178 is retired: it aliases N001–N114, all now derived at the installed source
instance. This changes all-retained count by one extra alias, with **zero**
independent/deduplicated discharge credit. L168 remains retired by Rc3.
L178's retirement does not retire source/extraction/artifact association.

## Exact before/after and dictionary scope

Before: Rc3 takes `primitiveOwner` at `Rc3_Install.configuration c reservation`
and returns its source-sampler continuation guarded by query/geometry/domain/
mul/one/inverse contracts, with model law-bearing carriers.
After: Rc4 takes `indexError : CoreError` as constructor DATA, no prepare or
primitive owner; returns all retained root conclusions plus the strengthened
result at `Rc4_Install.configuration indexError c reservation`. It computes
model public/address-fit and matching Data, and supplies all61 laws. The
same f/s/outer/pre/middle/fs/ss/run/tx2 tuple is reused throughout; no separately
existential native execution or model Context is joined.

The dictionary is EXACTLY Rc3 with SAQ's query and geometry installation,
and EXACTLY SAQ with Rc3's source-circle installation (`Rc4_Install.rc3/saq`).
It equals the original Rc3 dictionary iff
`SAQ_Decoder.install c.query = c.query` AND
`SAQ_Constructor.install indexError c.geometry = c.geometry`
(`exact_scope`,001). All other configuration fields are retained relative to
Rc3. SAQ replaces source arithmetic/basis/line/decoder callbacks and the source
geometry/inverse/fibre constructor; the error datum selects the fibre failure
value. The explicit body/slot expansions are056/060 and the upstream source
pin packet. This is a source-instance theorem, not a weakening over arbitrary
callbacks. Deployment does **not** presently instantiate equality to an
arbitrary old seed: the root extraction premise is explicitly specialized to
this dictionary, while its actual native/source-to-ELF/error-constructor
association remains open (L186 and existing extraction/runtime boundaries).
No source substitution is silently attributed to frozen binaries.

## Remaining ownership and non-vacuity

Actual remaining P: lead15, session A31, external3. Session A31 =12 round
return/evaluation laws +3 newWeights/pair/dot return equations +10 pairing
laws +1 matching +3 semantic endpoint +1 dot +1 canonical-observation family.
They retain their original owners; SAF_ coverage receives no closure credit.

All retained P coverage (including aliases): CPH_9; PFin_1; F3X_6; SAF_31;
P6B_5; UNCOVERED13. Deployment aliases included in these numbers are not
independent gates. UNCOVERED includes accepted1/2 event guards, proof/public
P2Prime association, external budgets, S6 native transport, library/native
frame, batch lowering, source-to-ELF and final release gates.

`Rc4_Nonvacuity.contracts` derives all three source-owner contracts for every
seed/error value. `model_surjective`/`data_surjective` preserve all old model
inputs and successful decoder-produced inputs. Four reverse transports
recover the entire original Rc3 result with the SAME witnesses. Rc3's accepted
same-proof/public/tag2/1880-byte input and not-all-reject witness remain in
that result under existing history/P2Prime guards. Historical successful exact
ELF/runtime evidence hashes were rechecked; those executions were not rerun.
This is not joint inhabitation of all runtime/crypto/compatibility hypotheses.
In particular the retained frozen2 exact-log compatibility guard is not
claimed satisfiable for deployment. Frozen3 and RuntimePersistence/game(a–d)
are APPROVED, not awaiting decisions; charged frozen3 integration remains work.

## Validation and frozen boundary

60/60 Lean compiles (52 pass,8 retained excluded diagnostics),0/0 Kani;
no further Lean launches. New Statement/Assemble split replaces default-
heartbeat failures011/012/014;002–004/006/017 were ordinary development errors.
No wall timeout, memory kill, cap increase, unchanged-input rerun, infrastructure
repair or package replay. All host jobs used the unchanged S2W launchers and
reservation barrier, one admitted scope at a time,6G/8G/swap0/tasks64,
-j1 -M7000 -DElab.async=false. No barrier contention/retry occurred.

Focused fresh audits028–060 cover root/conclusion/result/continuation/raw
carriers, all changed and retained field families, trust/extraction/runtime,
finish, history, parser, bank and deployment P6 boundary. Every new theorem's
#print axioms uses only propext/Classical.choice/Quot.sound. Section6 command,
source revision+hash/deps/status/wall/RSS/swap/axioms are in per-attempt receipts.
Top022: exit0,7.1109009819920175s,5376440KiB peakRSS,swap0,
revision90af2a9c9f plus exact dirty source snapshot. Final axioms059:
exit0,6.631484054028988s,5347532KiB,swap0,revision5f026d6155 plus audit snapshot.
The final source/object inventory checks all48 prefix sources and87 direct
objects/companions;1381 inherited source/non-vacuity file checks pass.
This is coherent-cache focused composition, not a fresh frozen release replay.

No shipped or cfg(kani) source changed, so no ELF rebuild trigger. Inherited,
not freshly reproduced: default f8c0ec72621fd5029a97d796c4a3623d0dc44a8e7074122372f9872915d143d4;
devnet63ad3e9cc096dcbb55b3ca7ac7c8e89e6a845796ab5e4f5b7d15db96f3784299;
Pool121f3e29741f510e6dc42d0345fc3c36217600f0be337094855c4a9da2581548.
No worktree/candidate owned by session A or another worker was edited. No
running-job result was imported or waited for. No keys or funds were touched.
