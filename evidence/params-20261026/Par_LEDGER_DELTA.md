# Parameter ledger delta

Owner-authorised free-parameter specialisation, not a protocol/source change.
S2 OPEN; the100-bit target is not yet established. Shared ledger left untouched
for lead/Cons_ reconciliation. Prefix-owned deliverables:

| Row | Before | After specialised instance |
|---|---|---|
| L085 p.hL | arbitrary p carries34+D≤N | REMOVED: Par_Parameters.address_bound, D3717,N131072 |
| L086 p.encLen | arbitrary p carries bound for all encodings | REMOVED: encoder_bound for original bounded raw-message carrier and identity enc |
| L087 p.decEnc | arbitrary p carries decoder inverse | REMOVED: decoder_inverse of original selected bounded-byte decoder |
| L151 i.data.Functional.map_add | model LinearMap structural law | DISCHARGED as instance: input_map_add on original i.data.F j/F0 |
| L152 i.data.Functional.map_smul | model LinearMap structural law | DISCHARGED as instance: input_map_smul on same maps/scalars |
| L153 tr.statement.initFits | bound field on free model public carrier | DISCHARGED at accepted public instance: Par_Public constructs carrier from same cuts, exports1880 and fit; Par_Transcript.accepted_initFits transports along original public-byte association |

No changes to any other row. L151/L152 remain intrinsic fields of the ORIGINAL
LinearMap type; no structural type is rewritten. They require no separately
supplied law, and establish no native arithmetic implementation. L153's physical
association is retained exactly: the transcript-bound theorem uses the explicit
same-byte equation, does not prove it from hash equality, and never projects the
existing initFits field to prove the bound. The same-cut accepted input constructor
needs no physical-association/public-length/initFits hypothesis from the caller.
No claim is made for an unassociated arbitrary public byte list.

## Exact before and after

Before: DrvC_NativePair.accepted_pair_driver quantifies M,Cv,N and arbitrary
p:FS2.Duplex.Params M Cv N; its acceptance consumer quantifies i and requires
its two physical byte associations. See original lean/DrvC_NativePair.lean and
full explicit #check in Par_007/stdout.log (first statement).

After: Par_NativePair.accepted_pair drops M,Cv,N,p and instantiates the EXACT
SelectedTranscriptParams.params. It existentially constructs i from SAME f.pub
and f.proof, proves its associations, tag2,length1880 and fit, and derives driver
acceptance/non-reject-all under the original history/P2prime. The quantified
native input bytes, cuts, errors, checkpoint and successful-run boundaries do
not change. The result specialises the formerly arbitrary i; it does not prove
all i have1880 bytes. Original root/length and other non-target binders remain.

Par_Headline.deployed exports that result AND the original installed DrvC
headline at DrvC_FirstConstants.configuration c. Same dictionary, native pair,
hashv, driver and accounting source. The headline's raw/binding/q-bound/adversary/
project hypotheses and Claims/failure/conclusion are unchanged. DrvC's existing
headline already fixed the selected model and had no p/linearity/initFits law
binders: the discharge is in its concrete predecessor and model instances,
not a claim that redundant wrappers remove further hypotheses. Explicit before/
after installed statements are third/fourth #checks in Par_007/stdout.log.

No new typeclass or structure bundles a removed assumption. No new cryptographic
hypothesis, field, failure event, probability law, extraction guarantee, security
metric or source refinement premise is introduced. No native-to-ELF closure is
claimed. The theorem is a conjunction composition, not a proof that this native
witness equals an arbitrary adversary's full experiment; L157/L159 retain that.

## Non-vacuity

Par_Parameters.parameter_nonvacuity constructs an actual bounded empty message.
The public bound is1955≤131072, from actual accepted decoded size1880.
Par_NativePair.accepted_pair and Par_Headline.deployed export a successful Input
and exclude reject-everything under the SAME original checkpoint history/P2prime.
Native acceptance remains an explicit original hypothesis. We reuse the retained
successful exact-default-ELF two-TX fixture and source audit documented in
../driver-inst-20261026/DrvC_fixture-audit.json and DrvC_HANDOFF.md; no fresh native
fixture or kernel joint inhabitance of all runtime/trust hypotheses is claimed.

## Frozen source/model scope

Model M={bs:Bytes // length≤3717}, Cv=WideExact, N131072,D3717,33 rounds,
identity raw-message enc, bounded-byte dec, labels160+i, original sigma/iv.
N and D are model finite-address/message bounds, not claimed Rust constants.
The source's r1_wire.rs row_shape and strict parse_record use tag+u32 length+
payload; row25 has(87+29)*32=3712 payload bytes and5 framing bytes. The selected
CircleRecordCodec first_length matches3717, and OpeningRecordCodec bounds its
other rows. No values, field representations, message codecs or rows change.
The generic bounded-message decoder is the model codec, distinct from the actual
1880-byte semantic public decoder. Source-to-model refinement remains the original
installed/source boundary; this job proves its parameter laws and specialises.
