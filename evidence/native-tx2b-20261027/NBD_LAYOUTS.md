# Byte-layout and rejection audit

Source inspection only, against frozen4bb3b3f5. Every ordered branch and byte range is retained verbatim in NBD_FROZEN_MEMBERS.md with full file/body pins in NBD_MEMBERS.json. The tables below are a review index, NOT proof of the unclosed codecs. Ranges are half-open; integer stores are little-endian. All digests are eight ordered four-byte limbs.

## U03

ASJA (688 bytes): magic[0,4), transport version[4], tree storage version[5], digest version[6], success byte1[7], next_pair_index[8,16), root[16,48), frontier row k[48+32k,80+32k), k<20. Decoder order: length, magic, transport version, tree format, digest version, success byte, root canonicality, twenty ordered frontier decodes, index load, afterstate validation. Thus noncanonical root/frontier can precede InvalidAfterstateIndex. Validator rejects index0 or >2^20, then root and each frontier canonicality; capacity itself is accepted. Encoder validates first, then writes exact fields.

ASPLIVE1 (800 bytes): magic[0,8),version[8],zero[9,16),pair-format binding[16,48),pool[48,80),deployment[80,112),sequence[112,120),next_pair_index[120,128),root[128,160),frontier k[160+32k,192+32k). Encoder checks output length before validation; validator order: zero pool/domain, sequence!=index, index>=2^20, root/frontier canonicality. Snapshot capacity is REJECTED, unlike afterstate capacity.

ASPLATE1 (1520 bytes): magic[0,8),version[8],itemcount2[9],header-width32[10,12),snapshot-width800[12,16),afterstate-width688[16,20),total1520[20,24),zero[24,32); SAME snapshot[32,832),SAME candidate afterstate[832,1520). Encoder checks output width first and checked_add(snapshot.index,1)==Some(candidate.index) before filling/writing output; then snapshot and afterstate codecs with their distinct wrapped errors. Failure after fill can retain prefix mutations: a whole Result equality must preserve this mutable output, not just the error tag.

## U04

| Image | Exact fields |
|---|---|
| ASPI (144 bytes) | magic0..4,v4,zero5..8,pool8..40,mint40..72,token72..104,asset104..108,zero108..112,deployment112..144 |
| ASPP (104 bytes) | magic0..4,v4,flags5,zero6..8,registry_program8..40,authority40..72,policy72..104 |
| ASM8 (384 bytes) | magic0..4,v2at4,lanes8at5,digest-version6,bump7,format8..40,next_checkpoint40..48,initialized_mask48,boolean49,zero50..64,ASPI64..208,ASPP208..312,zero312..320,eight lane-sequences320..384 |
| ASC8 (192 bytes) | magic0..4,v2at4,lanes8at5,digest-version6,bump7,master8..40,deployment40..72,checkpoint_sequence72..80,root80..112,eight lane-sequences112..176,zero176..192 |
| ASRG (128 bytes) | magic0..4,v2at4,flags5,bump6,zero7,pool8..40,authority40..72,policy72..104,generation104..112,delay112..120,zero120..128 |
| ASRE (192 bytes) | magic0..4,v2at4,status5,statement_version6,bump7,pool8..40,verifier40..72,profile72..104,release104..136,activation136..144,retirement144..152,policy152..184,zero184..192 |
| ASR2 (256 bytes) | magic0..4,v3at4,flags5,mode1at6,bump7,pool8..40,authority40..72,policy72..104,generation104..112,delay112..120,registry_program120..152,loader152..184,programdata184..216,executable_hash216..248,programdata_bump248,zero249..256 |
| ASE2 (320 bytes) | magic0..4,v3at4,status5,statement_version6,mode1at7,pool8..40,verifier40..72,profile72..104,release104..136,loader136..168,programdata168..200,hash200..232,expected_authority232..264,activation264..272,retirement272..280,policy280..312,bump312,programdata_bump313,zero314..320 |

Identity decoder: length/magic/version/reserved before raw asset<P. Policy decoder: envelope/reserved before policy validator. Policy validator: unsupported flags, zero registry/policy, deployment-immutable implies registry-immutable, then immutable flag iff authority is zero. It does NOT itself require immutable or unpaused operation: those are authentication-caller checks.

Master decoder: envelope, reserved, format, boolean, identity, policy, eight sequences, validate_master. Master validation requires nonzero pool/mint/token/domain, valid policy, sequences<=2^20, and consistency of has_checkpoint with next sequence and all-zero previous sequences. initialized_lane_mask is an unconstrained u8 here. Pool checkpoint decoder checks envelope/reserved, nonzero master/domain, root canonicality, then each sequence<=2^20. No1768-byte verifier checkpoint is decoded here.

Registry decoders check length/magic/version, V2 deployment mode, reserved, then status conversion (entry only), fields, validator. V1/V2 registry validation: flags mask3, all required bindings nonzero, immutable iff authority zero, delay>0. V2 additionally requires nonzero registry/loader/programdata/hash. Entry validation: statement_version!=0, required bindings nonzero, V2 expected authority allzero, and retirement==u64::MAX OR retirement>activation. Status conversion accepts0..3 only. is_active_at uses status1 AND activation<=slot AND (retirement==MAX OR slot<retirement), so the retirement endpoint is excluded. Pause/immutable flag masks are1/2, distinct from policy masks in meaning.

## U05

ASQ8 (320 bytes): magic[0,4),version[4],kind1/2[5],digest-version[6],zero[7],profile[8,40),release[40,72),Pool-program[72,104),payment[104,320). Decoder order: length/magic/version/kind/digest-version/zero, variant payment decoder, then nonzero profile/release/Pool-program. A zero binding does NOT skip earlier malformed payment errors.

ASF8 (1880 bytes): magic0..4,version4,kind5,digest-version6,output_lane7,master8..40,checkpoint_account40..72,selected_lane72..104,checkpoint_sequence104..112,historical_anchor112..144,ASPLATE1 at144..1664,payment1664..1880. Therefore live snapshot[176,976),candidate ASJA[976,1664); live deployment is public[256,288), NOT[208,240).

ASF8 validator order: nonzero three account IDs, lane<8, payment encode/validation, payment pool==master, payment deployment==snapshot deployment, snapshot.pool==master, anchor_sequence==checkpoint_sequence, anchor==historical_anchor, canonical nullifier/output-lane selection, full late statement encoding. Preserve every wrapped Payment/Account/LaneTransition error. Encoder validates before emitting fields, then re-encodes the same late/payment data; no reselected statement.

ASR8 (792 bytes): magic0..4,version4,kind5,digest-version6,lane7,master8..40,selected_lane40..72,nullifier72..104,SAME ASJA104..792. validate_result checks nonzero master/lane-account, canonical nullifier/lane selection, then afterstate encoding. Against-statement validator runs statement validation FIRST, result validation SECOND, then compares kind/master/lane-account/output_lane/nullifier/entire afterstate. No hash comparison substitutes for that exact identity.

## Fixture defects and caller domains

fixture-tx2w/JHf_GENERATOR_FINDING.json identifies the old support generator's master[176,208) and checkpoint[40,72) assignment from public[208,240). Correct source is public[256,288). These offsets follow the nested ASF8/live layout above. fixture-tx2u/JHb_TX2_HANDOFF.md separately identifies owner corrections: TX2 raw proof owner is unrestricted by readonly-buffer validation; Pool ownership belongs to slots1/2/3, registry ownership4/5, verifier ownership6. These are fixture-generation defects, not shipped bugs; codec success by itself proves neither owners nor PDA authenticity. Existing fixture bytes/keys/candidates are untouched.
