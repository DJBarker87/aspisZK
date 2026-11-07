# Field records: (struct, field, rows, cls, adapter, exists, flag, note)
# cls: DEF | TRUST | ROOT
# exists: module/job string if an installation term exists in a merged job, else None
F = []
def f(struct, field, rows, cls, adapter, exists=None, flag=None, note=""):
    F.append(dict(struct=struct, field=field, rows=rows, cls=cls, adapter=adapter,
                  adapter_exists=exists, flag=flag, note=note))

# ---------------- PoolLib (RSL_Pool.lean) ----------------
P='PoolLib'
f(P,'Request',[],'DEF','carrier := emitted PoolV1PairForestTerminalRequestV1 of the copy used by TX2:163 roots (NFY_Part059); identify with the AdapterRw copy',None,None,'opaque carrier; must be the TX2:163 output type')
f(P,'Statement',[],'DEF','carrier := emitted PoolV1PairForestTerminalStatementV1 (TX2:224 output = TX2:165/219 input); one copy for all three',None)
f(P,'Afterstate',[],'DEF','carrier := scan_proof_buffer candidate afterstate (TX2:226 output = TX2:224 input)',None)
f(P,'decodeRequest',['TX2:163'],'ROOT','Slice U8/Std.Result(Result Request DecodeErr) -> Bytes -> Option Request (byte image + Ok/Err->some/none); all lengths','NMS_ NMS_R2DecoderImage.full, NMS_R2RequestBranches (partial)',None,'NMS_REMAINING: concrete request B32 byte representation still to fix')
f(P,'reqProfile',[],'DEF','field read; [u8;32] -> B32 adapter','NMS_ NMS_R2Gated242 (literal key guards)')
f(P,'reqRelease',[],'DEF','field read; [u8;32] -> B32 adapter','NMS_ NMS_R2Gated242')
f(P,'reqPoolProgram',[],'DEF','field read; [u8;32] -> B32 adapter','NMS_ NMS_R2Gated242')
f(P,'reqNullifier',['TX2:158'],'ROOT','native eight-word nullifier array -> B32 (32 bytes) representation','NMS_ NMS_R2NullifierCarrier.full (partial: B32 byte rep not fixed)')
f(P,'outputLane',['TX2:156'],'ROOT','B32 -> Option UInt8 from lane_instance model; nullifier byte link','NMS_ NMS_R2LaneModel.full (partial: outputLane link open)')
f(P,'decodeMaster',['TX2:153'],'ROOT','NJY_Master.model (Cut-indexed, functional model) -> Option RSL.Master field-by-field (PoolIdentity, VerifierPolicy, Digest=List UInt32)',None,None,'RSL comment cites TX2:218 (the Box wrapper, transcribed as decodeMasterBox); the decoder itself is TX2:153. NND A2/233 lists the payload decoder as remaining')
f(P,'decodeCheckpoint',['TX2:152'],'ROOT','NJY_Checkpoint.model -> Option RSL.Checkpoint',None,None,'RSL comment cites TX2:216 (Box wrapper); decoder is TX2:152')
f(P,'validatePolicy',['TX2:151'],'ROOT','is_ok of NHY_PolicyModel on VerifierPolicy carrier','NND_ NND_RegistryLibrary.install / NND_PolicyValue.native',None,'NND link is to AdapterRw op15; LIB must also tie it to NHY_PolicyModel.actual_slot')
f(P,'decodeRegistryV1',['TX2:203'],'ROOT','Option image of NJY_Roots.registry model','NND_ NND_V1DecoderValues.registry',None,'NND link is to AdapterRw op31; tie to NJY_Roots.registry')
f(P,'decodeRegistryV2',['TX2:204'],'ROOT','Option image of NHY_RegistryJoin.cohort','NND_ NND_V2DecoderValues.registry',None,'tie to NHY_RegistryJoin.cohort')
f(P,'decodeEntryV1',['TX2:201'],'ROOT','Option image of NJY_Roots.entry','NND_ NND_V1DecoderValues.entry',None,'tie to NJY_Roots.entry')
f(P,'decodeEntryV2',['TX2:202'],'ROOT','Option image of NIJ_EntryJoin.cohort','NND_ NND_V2DecoderValues.entry',None,'tie to NIJ_EntryJoin.cohort')
f(P,'scanProof',['TX2:226'],'ROOT','RS image incl. Box site; byte image of the 58295-byte buffer','NMS_ NMS_R2PoolSites.scan (+NMS_R2N_ScanSites.interpreted, scanner_extent)',None,'representation image of a fixed source model; NMS: not a physical producer certificate')
f(P,'reconstruct',['TX2:224'],'ROOT','RS image incl. both Box-site aborts; Authenticated carrier map','NMS_ NMS_R2PoolSites.reconstruct (+NMS_R2N_ReconstructSites.meaning)')
f(P,'encodeStatement',['TX2:165'],'ROOT','[u8;1880] by value -> Spec (Option Bytes), no allocation arm',None,None,'NMS_REMAINING: fix the CLOSED 1880-array encoder law')
f(P,'emitResult',['TX2:219'],'ROOT','RS Unit with the returnData event (sol_set_return_data)',None,None,'NMS_REMAINING: return-data child law not installed')
# ---------------- DeployedIds ----------------
f('DeployedIds','pool',['TX2:220'],'ROOT','.rodata 32-byte constant -> B32 literal',None,None,'trivial; NMS_R2Gated242 already uses the frozen deployed-pool value')
f('DeployedIds','registry',['TX2:225'],'ROOT','.rodata 32-byte constant -> B32 literal',None)
# ---------------- V2Lib (RSL_TX2_241.lean) ----------------
V='V2Lib'
f(V,'VErr',[],'DEF','carrier := verifier::Error (8 variants); SAME copy as NMN_064 error carrier and VLib.VErr',None)
f(V,'debug',['TX2:211'],'ROOT','NGL_ErrorModel.label/message: Debug string of verifier::Error','NMS_ NMS_R2ErrorSource.full (partial)',None,'CLOSED law has no format! allocation; harmless: impl subset Ref because Ref admits the returned arm')
f(V,'Root0',[],'DEF','NLP_InputDomain.Root0 on byte carriers (headline domain predicate, not a ledger row)','NNC_ WeakR0Rep.at_entry, NNC_ByteCarriers')
f(V,'tx2auth',['TX2:064'],'ROOT','NMN_064.RowSpec Law + chronology over NLW_Full064.Frame/End -> Bytes^3 -> Spec (Except VErr Unit), abort = prefix',None,'F1(resolved rev3)','canonical rendering (TAS name NMN_064.rslRefines) not built; NNC_ObservedLaw.w + contains_native cover only the weak (Root0-free) library. Resume fills (verifier.rs:428) read Env.reservation (rev3); the law must be Spec.Functional on Dom064')
# ---------------- S1Lib (RSL_TX1_345.lean) ----------------
S='S1Lib'
f(S,'Statement',[],'DEF','carrier := emitted terminal statement of TX1:332 (NMT Statement)','NMT_ NMT_R2_ConcreteS1.library')
f(S,'decodeStatement',['TX1:332'],'ROOT','1880-byte slice decode -> Option Statement','NMT_ NMT_R2_ConcreteS1.decode (partial: total decoder transport open)')
f(S,'decodeReachesAlloc',['TX1:332'],'ROOT','Bool: decoder reached a Box site',None,'F4','no TX1:332 root mentions an allocation site (all 28 are allocation-free); NMT_R2_ReachLibrary.reaches is source-derived (NMT_R2_Reach*, wrong-length lemma) without the association')
f(S,'validateStatement',['TX1:276'],'ROOT','is_ok of the validator Result','NMT_ NMT_R2_PublicLibrary.valid')
f(S,'encodeCandidate',['TX1:278','TX1:267'],'ROOT','encoder of common().lane_transition.candidate_afterstate -> Option Bytes','NMT_ NMT_R2_ConcreteS1.encode (partial: total encoder transport open)')
f(S,'semanticPublic',['TX1:268'],'ROOT','statement.semantic_public() -> VLib.Public','NMT_ NMT_345.semanticValue via NMT_R2_ConcreteS1.library')
# ---------------- VLib (RSL_Verifier.lean) ----------------
L='VLib'
for c,ty in [('Public','r0::Public (NMT Public / NKR_TermPublic), shared with S1Lib.semanticPublic codomain'),
             ('Prefix','parsed Prefix that remembers its source bytes: 129/134/142 roots are stated on bytes with parse bytes = ok pre; AspisR1PrefixAggregateParser -> AspisR1PublicPreparation via PrefixAdapter.fromOld'),
             ('Transcript','SemanticTranscript<SolanaDigest>'),('Challenges','r1_wire::Challenges'),
             ('OrigChallenges','state_only_prefix::r0::Challenges'),
             ('QM31','canonical subtype {x : NQ // canonQ x} (needed for total qadd/qmul)'),
             ('Alpha','[QM31;10] over the canonical carrier'),('Claims','Box<[[QM31;29];3]>'),('K29','[QM31;29]'),
             ('Point','SecureCirclePoint'),('Record','r1_wire::ValidatedRecord'),('WErr','r1_wire::Error'),
             ('VErr','verifier::Error, SAME carrier as V2Lib.VErr'),('CodecErr','compact::CodecError'),('View','verifier::View'),
             ('Prepared','verifier::Prepared'),('E29','[E;29] (WideExact copy used by TX1:179/186)'),('Acc','verifier::Accumulator'),
             ('Geo','verifier::QueryGeometry'),('Weights','verifier::BatchedWeights')]:
    f(L,c,[],'DEF','carrier := '+ty,None,None,'one emitted copy per carrier across all child roots; cross-copy identifications are carrier adapters')
f(L,'qDec',[],'DEF','DecidableEq on the canonical QM31 carrier',None)
f(L,'pDec',[],'DEF','DecidableEq on Point',None)
for c in ['wTerminal','wEqualCirclePoints','wPublic','vParse','vSemantic','vAllocation']:
    f(L,c,[],'DEF','constructor of the emitted error enum',None)
f(L,'codecToV',[],'DEF','impl From<CodecError> for Error (candidate.rs:22): constant Parse; no ledger row (inlined); one lemma on the emitted From body',None)
f(L,'debugV',['TX1:NGB001'],'ROOT','NGL_ErrorModel.label (shared with V2Lib.debug)',None,None,'same function as TX2:211; no TX1-side installation yet')
f(L,'finishInputDom',[],'ROOT','conjunction of the 136 child clauses that 136 cannot discharge internally (ledger NJW-caller 134/142, NKN-caller 129, NLS-bf 256 hd..asset, NLS-context)',None,'F7','ledger clause records, not a root; several are prose and need a Lean transcription; canonicality clauses hc..hm need 129/142/150 exports or must be carried here and derived by 137 from begin')
f(L,'publicDom',[],'ROOT','NLS-bf:TX1:136:TX1:256:hd = NKR_DigestChildren.Domain (NKR_TermPublic.value pub)','NMT_ NMT_345PublicDomain.publicDomain; NMT_R2_PublicLibrary.withPublic; discharge NMT_345.validated_public_domain')
f(L,'semanticBytesDom',['TX1:138'],'ROOT','NGX_PrefixCarrier.producer_domain on the byte argument',None)
f(L,'checkValuesDom',['TX1:179'],'ROOT','NHS_PreparedPacket.source premise compact_check (check_values compact = ok (Ok ())) on the 464-byte y1 slice, verbatim',None,'F2(resolved rev3)','RSL rev3 field: own-input clause (R4) of TX1:087; discharged at 094 by TX1:084 canonical_scan (TX1_094.R4Discharge, to be proved from NKL_ScanRoot)')
f(L,'semanticRounds',['TX1:134'],'ROOT','graph of the NJM rounds model at SAME (Prefix, Transcript); Cut-indexed root -> deterministic law; dom = NJW-caller 134 clauses',None)
f(L,'claims',['TX1:129'],'ROOT','graph of NKA claims reference incl. Box carrier; dom = NKN-caller 129',None,'F1(resolved rev3)','root quantifies allocator/reservation; heap::uninit at r1_semantic.rs:45 returns Err(Allocation); rev3: instantiate the reservation with Env.reservation (Spec.tryReserve), law Child.Functional')
f(L,'origChallenges',[],'DEF','struct literal (r1_semantic lines 239-246)',None)
f(L,'terminalQm31',['TX1:256'],'ROOT','NLH_WrapperRoot.source law; dom = NLS-bf 256 clauses','NMT_ NMT_R2_PublicLibrary.withPublic (Public transport only)')
f(L,'maskValue',['TX1:076'],'ROOT','NHU_Mask.result value on canonical carriers',None)
f(L,'validatedRecord',['TX1:141'],'ROOT','NFU_PrefixRecords.validated_record (equation); row U8 vs Nat index adapter',None)
f(L,'decodeK29',['TX1:147'],'ROOT','NGO_CallCases / NGO_DecodeComposed value',None)
f(L,'eta',[],'DEF','field read',None)
f(L,'qadd',['TX1:024'],'ROOT','QM31::add Ok value on canonQ inputs, closed under canonC',None,'F5','ledger root NEB_ArrayRefs.qm_injective is not a value law; the value law is certificate theorem NEB_QMCalls.add (+NEB_AdditiveFrames.qm_add)')
f(L,'qmul',['TX1:029'],'ROOT','QM31::mul Ok value on canonQ inputs',None,'F5','ledger root AspisR1.NFS_QueryLoopRoot.root is the query-loop root, not a mul law; value law is NEB_QMCalls.multiply (+NEB_FieldFrames.qm_mul)')
f(L,'at28',[],'DEF','extra[28]',None)
f(L,'state',['TX1:146'],'ROOT','NGX_StateImpl.source/state_effects (pure, no event)',None)
f(L,'circle',['TX1:142'],'ROOT','graph of NJM circle model; dom = NJW-caller 142',None)
f(L,'payload',['TX1:139'],'ROOT','NGX_Payload.source/tail_total',None)
f(L,'c1Root',[],'DEF','*prefix.c1_root field read',None)
f(L,'parsePrefix',['TX1:138'],'ROOT','NGX_PrefixCarrier.full_result into the parsed-Prefix carrier','NMP_ parse138 full Result/type inverse at identical bytes (partial)')
f(L,'publicTranscript',['TX1:131'],'ROOT','NHG_Lengths/NHG_PublicCarrier/NHG_PublicTranscript with digest events from Env.sha256','NMP_ public131 adapters, NMP_Transcription137 (partial: digest/allocation prefixes open)')
f(L,'begin',['TX1:150'],'ROOT','NGX_BeginDomains/NHG_BeginFrame with digest events','NMP_ begin150 adapter (partial)')
f(L,'filled',['TX1:064'],'ROOT','heap::filled law (NGC_ReferenceValues.heap; same function as TX2:045 NIG_FilledCoverage.source)',None,'F1(resolved rev3)','fallible try_reserve_exact (r0/heap.rs:5-10); rev3: Err iff Env.reservation = false (Spec.tryReserve), law Child.Functional')
f(L,'expandSemantic',['TX1:098'],'ROOT','NGV_* expansion law (src, dst) -> written dst',None,None,'NMP: concrete expansion interpretation still to install')
f(L,'expandValues',['TX1:099'],'ROOT','NFU_CompactLeaves.expand_result',None)
f(L,'wideView',['TX1:095'],'ROOT','NHF_View*/NEO_FieldView/NET_WideModel',None)
f(L,'viewSemantic',[],'DEF','v.semantic field read',None)
f(L,'parseShape',['TX1:086'],'ROOT','NJS_Parse.source (NJS_Extract = Op3I_Source copies)',None)
f(L,'canonicalScan',['TX1:084'],'ROOT','NKL_ScanRoot.deployed/adopted/success_events',None)
f(L,'zeroE29',[],'DEF','[E::ZERO;29] literal',None)
f(L,'accNew',['TX1:174'],'ROOT','Accumulator::new(S2) law (NGC cohort roots)',None,'F1(resolved rev3)','calls heap::filled (verifier.rs:93): Err(Allocation) iff Env.reservation = false (rev3), law Child.Functional')
f(L,'batchMerkle',['TX1:081'],'ROOT','NLN_TX1_081.root; dom = NLO-bf:TX1:094:TX1:081:64-67 (len, wire, canonical queries, rootValues)',None,None,'094 discharges dom from parseShape and from P (query range, root bindings): see F3')
f(L,'geometry',['TX1:181'],'ROOT','NFN_NFB_GeometryComposed.result_state_effects',None)
f(L,'weightsNew',['TX1:176'],'ROOT','NJZ_Weights.new_source (AdapterRw/VTop copy)',None,'F1(resolved rev3)','calls heap::filled (verifier.rs:207); ledger caller clause NKH asks for both reservation arms: both arms now selected by Env.reservation (rev3), law Child.Functional')
f(L,'queryLoop',['TX1:088'],'ROOT','NFG_QueryLoopSource.complete / NFP / NFS roots',None)
f(L,'finish',['TX1:175'],'ROOT','BatchedWeights::finish (NGC_FinishContents.contents)',None)
f(L,'checkpoint',['TX1:186'],'ROOT','NHS_CheckpointPacket.source; dom := DriverEstablishedDomain (op3/op4/op7/op12 Ok, heap reservation Ok) at SAME proof',None,'F6','root is conditioned on predecessor results and on allocation success; the Vec abort arm named in the RSL comment is not exposed')
# ---------------- PreparedNew ----------------
f('PreparedNew','P (dom, law)',['TX1:179'],'ROOT','NHS_PreparedPacket.source + error/abort companions at SAME (Verified, View, g)','NMP_ fresh source call and g result (partial)','F2,F3','root is Ok-arm only (premises semantic_finish, compact_check, returned = ok); 179 domain needs compact464 checked: rev3 (R4) on 087 now supplies it; F3 (Ok-arm-only law) remains')
# ---------------- Env group (TAS Sig) ----------------
E='Env/EnvRep'
f(E,'Env.sha256',[],'TRUST','SolanaDigest via sol_sha256 (TX1:327/TX2:210 NGC_DigestBridge.forwarding) bound to the headline syscall/p1','NNC_ NNC_RuntimeOracle, NNC_DigestTrace (partial)')
f(E,'Env.pda',[],'TRUST','create_program_address reply, ruling (at) quantified slot','NND_ NND_RuntimePartial (partial)')
f(E,'Env.clock',[],'TRUST','RuntimeClockSlotBinding (clock := .ok slot at TX2)','NNE_ NNE_Clock')
f(E,'Env.reservation',[],'TRUST','RSL rev3: try_reserve reply (true = Ok), bound in EnvRep to the headline binder reservation : NP6_StdModel.Reservation (env.reservation = true <-> reservation = .Ok ())',None,'F1(resolved rev3)','single reply for every try_reserve occurrence, same shape as NP6_StdModel.calls')
f(E,'EnvRep (+env1_rep, env2_rep)',[],'TRUST','agreement of env with the ctx runtime oracles','NNE_ (host definitions, NNE_RecordSig)','F1(resolved rev3)','RSL rev3: EnvRep also binds Env.reservation to the headline reservation binder (TAS_Interfaces EnvRep docstring); the host definition must include that conjunct')
f(E,'readerHeader',[],'TRUST','NLW_ReaderHeader.decode ck = some (h pr, h pub)','NNC_ NNC_ObservedLaw.accepted_header')
