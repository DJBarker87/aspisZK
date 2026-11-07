import json, sys, collections
sys.path.insert(0, '.')
from LIB0_fields import F
led = json.load(open(sys.argv[1]))
rows = {r['row']: r for r in led['rows']}
def rowinfo(rid):
    r = rows[rid]
    return dict(row=rid, status=r['status'], function=r['function'], owner_module=r['owner_module'],
                roots=[x['root'] for x in r.get('root_owners', [])])
for x in F:
    x['supplying'] = [rowinfo(r) for r in x['rows']]
    assert all(s['status'] == 'CLOSED' for s in x['supplying']), x
    if x['cls'] == 'DEF': x['status'] = 'definitional'
    elif x['cls'] == 'TRUST': x['status'] = 'trust-row'
    elif x['flag'] and any(t in [u.strip() for u in x['flag'].split(',')] for t in ('F1','F2','F3','F4','F6')): x['status'] = 'unsupplied-or-partial'
    elif x['adapter_exists']: x['status'] = 'root+adapter-exists'
    else: x['status'] = 'root+adapter-new'
TR = [
 ('readonlyBuffer', ['TX1:340','TX2:237'], 'exists in forest', ''),
 ('readonlyAccount', ['TX2:236'], 'new', ''),
 ('verifierCheckpoint (incl. data_len clone arm)', ['TX1:341','TX2:238'], 'partial', 'CLOSED packet restricted to snapshot error variants (NMT, NMX: NGL_LengthCarrier.domain); Domain-True rows need the unrestricted law, i.e. the transcription itself'),
 ('requireDistinct', ['TX1:339','TX2:235'], 'new', 'three (TX1) and seven (TX2) account forms'),
 ('requireZero', ['TX1:342'], 'exists', 'frozen suffix loop vs historical index loop: NND L117 symbolic equality'),
 ('OwnedAccount.data / data_len', ['TX1:335','TX2:229'], 'partial', 'NMS_R2GetterLink.full gives the unrestricted getter with clone arm; NHJ_DataPacket is restricted'),
 ('OwnedAccount.key', ['TX2:231'], 'new', ''),
 ('snapshot', ['TX1:343','TX2:239'], 'exists', 'NMV snapshot/window laws complete; snapAll_errs/snapAll_getters_plain in RSL_TX1_344'),
 ('is_active_at V1/V2', ['TX2:194','TX2:196'], 'new', ''),
 ('is_paused / is_immutable V1/V2', ['TX2:197','TX2:198','TX2:199','TX2:200'], 'new', ''),
 ('decodeMasterBox / decodeCheckpointBox', ['TX2:218','TX2:216'], 'partial', 'native Cut/Windows/Heap roots; NMX_REMAINING: instantiate their Box/allocator representations at SAME calls'),
 ('admitted / stage1Route', ['TX1:331','TX2:214'], 'new', 'NNF_ has the route lemmas over RSL'),
 ('decode_digest_canonical (217 body)', ['TX2:146'], 'new', ''),
 ('error / mapVErr', ['TX1:NGB001','TX2:211'], 'partial', 'NMS_R2ErrorSource.full on TX2; CLOSED law has no format! allocation (harmless direction)'),
 ('observer', ['TX1:329','TX2:212'], 'exists', 'None in the release build, ruling (al)'),
 ('r1_semantic::mark (no-op)', ['TX1:130'], 'missing lemma', 'F8: CLOSED NHU_Mark packet is None-only; RowSpec_136/137 quantify obs; frozen body is let _=(obs,i) without detail-phases'),
 ('verifier::mark', ['TX1:191'], 'exists', 'NEO observer root, None-only; 087/094 fix obs=None'),
 ('transfer/withdrawal_statement_box (inside reconstruct)', ['TX2:227','TX2:228'], 'inside NMS_R2PoolSites.reconstruct', ''),
]
trans = [dict(transcription=t, supplying=[rowinfo(r) for r in rs], adapter=a, note=n) for t, rs, a, n in TR]
FLAGS = {
 'F1': dict(fields=['VLib.filled','VLib.accNew','VLib.weightsNew','VLib.claims','V2Lib.tx2auth'],
   classification='demonstrable error in RSL rev2 (Env/nondeterminism)',
   evidence='crates/aspis-core/src/r0/heap.rs:5-10 (filled: try_reserve_exact -> Err(Allocation)), :11-14 (uninit); callers candidate.rs:256 (prepare), verifier.rs:93 (Accumulator::new), verifier.rs:207 (BatchedWeights::new), verifier.rs:428 (resume, TX2:064), r1_semantic.rs:45 (claims). The CLOSED roots quantify the reservation (NKA_ClaimsRoot.claims: allocator/state/reservation; NGC/NIG filled roots: reservation; NKH caller clause: both arms).',
   consequence='RSL.Env carries sha256/pda/clock only, so a fallible reservation outcome is not an oracle reply. A faithful Child law for these fields must admit both Ok and Err(Allocation) at the same arguments and Env, and impl : Args -> Env -> Obs cannot be the actual function. The RowSpec proofs are unaffected (a relational law admits the impl), but the TX1 returned path 345->328->094->087->filled/accNew/weightsNew and 136->claims becomes nondeterministic at fixed Env, so AMN.a1_forces_det makes A1 (NND_A1/A1min Err arm) and NND_Tx1ReturnedValues.returned unprovable; TX2 tx2auth gives the same for NND_Tx2Values.auth_ret. The rev2 header claim that the only nondeterminism is the aborting allocation site is false for try_reserve sites.',
   recommendation='lead applies a rev2 patch: add a quantified reservation reply to RSL.Env (ruling (at) shape, one reply per fallible site occurrence), make the four VLib children and the 064 law read it, and bind it in Sig.EnvRep to the headline reservation binder. Alternative (worse): an owner ruling that try_reserve failure is outside the obligation, which would be a trust addition. LIB builds every other field now and leaves these five behind a parameter until the lead rules.'),
 'F2': dict(fields=['PreparedNew.dom (TX1:087 call)'],
   classification='demonstrable error in RSL rev2 (TX1:087 Domain incomplete), unless the lead prefers a new TX1:179 law',
   evidence='TX1:179 root NHS_PreparedPacket.source has premise compact_check : check_values compact = ok (Ok ()) on the 464-byte y1 slice; ledger 179 inventory domain says "LPt compact464 checked". Frozen prepare (candidate.rs:255-264) runs expand_values (compact.rs:127-136, no canonicality check) and never calls check_values; only tx1 calls canonical_scan (candidate.rs:275) before prepare. RowSpec_087 Domain is R1-R3 only. NMP_REMAINING records the same gap ("179 canonicality").',
   consequence='With P.dom verbatim from 179 (the RSL rule), RowSpec_087 is unprovable: the parent cannot discharge the child domain at the call.',
   recommendation='add own-input clause (R4) "proof[7031..7495] passes check_values" to RowSpec_087, discharged in RowSpec_094 from the TX1:084 canonical_scan law at SAME proof. This narrows 087 only and does not propagate past 094.'),
 'F3': dict(fields=['PreparedNew.law','VLib.batchMerkle.dom discharge at 094'],
   classification='missing child lemma (TX1:179)',
   evidence='NHS_PreparedPacket.source is stated under semantic_finish/compact_check/returned = ok: Ok arm only. Missing: Err arms of t.queries(..)? and prepared_claim(..)? (verifier.rs:83,87), the Vec::with_capacity and Box::new abort arms (verifier.rs:78, 88), g on every arm, and the exports 094 needs for batch_merkle: queries[j] < 262144 and root bindings (NLO-bf:TX1:094:TX1:081:66/67).',
   consequence='PreparedNew cannot be instantiated with a complete law; 094 cannot discharge the 081 domain.',
   recommendation='prove from the same emitted Prepared::new body (NGN_Emitted.prepared) with the NHS/NFW/NHL support already used by the root; RSL_INDEX item 4 anticipated this.'),
 'F4': dict(fields=['S1Lib.decodeReachesAlloc'],
   classification='missing child lemma (TX1:332), not an RSL error',
   evidence='none of the 28 TX1:332 roots mentions an allocation site; Aeneas emits Box::new as pure, so the reached sites are visible only in source positions (pair_tree_profile.rs:665/675/742, pair_forest_terminal.rs:351/379/394). NMT has the source-derived definition NMT_R2_ReachLibrary.reaches and the wrong-length zero-allocation lemma.',
   consequence='non-blocking for RowSpec_345 and A1 (allocIf admits the returned arm for any Bool), but the gate requires the unique admissible instantiation.',
   recommendation='prove reaches = the decoder reached-site predicate from NMT_R2_Reach* plus the extraction item; record its reliance on source positions.'),
 'F5': dict(fields=['VLib.qadd','VLib.qmul'],
   classification='supplied by a CLOSED certificate theorem, not by the named ledger root (ledger hygiene); no RSL change',
   evidence='TX1:024 root_owners = NEB_ArrayRefs.qm_injective; TX1:029 root_owners = AspisR1.NFS_QueryLoopRoot.root; certificates cite NEB_QMCalls.add/multiply, NEB_AdditiveFrames.qm_add, NEB_FieldFrames.qm_mul (canonQ inputs).',
   consequence='LIB must cite the certificate theorems and use the canonical-subtype carrier so the functions are total.',
   recommendation='report the root-name mismatch to the ledger owner at the next ledger.'),
 'F6': dict(fields=['VLib.checkpoint'],
   classification='adapter plus missing child lemma (TX1:186 allocation-failure arm)',
   evidence='NHS_CheckpointPacket.source premises: parsed (op3), scan (op4), preparation (op7), newA (op12) = ok and allocation : NHS_PendingReservation.heap .. = ok. Ledger HYP DriverEstablishedDomain.',
   consequence='dom must be the existential predecessor history at SAME proof (discharged by 094 from its own earlier calls); the Vec abort arm is not exposed.',
   recommendation='install dom := DriverEstablishedDomain verbatim; prove the reservation-failure branch from NHS_PendingReservation (or fold it into the F1 channel if the reservation is fallible).'),
 'F7': dict(fields=['VLib.finishInputDom'],
   classification='open derivation; possible missing child lemmas (canonicality exports of TX1:129, TX1:142, TX1:150); not an RSL error yet',
   evidence='RSL_LEDGER_CLAUSES TX1:136: NLS-bf hd/hc/hp/hz/hl/hchi/ht/hm/asset, NJW-caller 134/142 (prose), NKN-caller 129 (prose), NLS-context.',
   consequence='until each clause is classified as internally discharged or carried, 137 cannot prove finishInputDom from parse/public_transcript/begin.',
   recommendation='LIB writes the clause-by-clause table and Lean transcription; carried clauses must be stated over (public, prefix, transcript, challenges) only.'),
 'F8': dict(fields=['(transcription) TX1:130 mark'],
   classification='missing child lemma, trivial (TX1:130 at arbitrary obs)',
   evidence='r1_semantic.rs:75-80: let _=(obs,i) without detail-phases; ledger packet None-only (NMP_REMAINING).',
   consequence='RowSpec_136/137 quantify obs.', recommendation='one lemma on the emitted no-op body.'),
}
ORDER = [
 ('LIB_Carriers', 'byte/array/Result/Obs adapters, Spec.graph and Child.ofFn, Returns glue (AMN_ReturnedPath, NND_Returned), emitted-copy identifications', []),
 ('LIB_Env', 'Env.sha256/pda/clock bindings (reuse NNC_RuntimeOracle, NNC_DigestTrace, NNE_Clock)', ['LIB_Carriers']),
 ('LIB_Deployed', 'DeployedIds', ['LIB_Carriers']),
 ('LIB_ErrorDebug', 'V2Lib.VErr/debug, VLib.VErr/debugV', ['LIB_Carriers']),
 ('LIB_Root0', 'V2Lib.Root0 and the NNC R0 byte link', ['LIB_Carriers']),
 ('LIB_Transcribed', 'transcription lemmas (bm)(2)(c)', ['LIB_Carriers','LIB_Env']),
 ('LIB_PoolCarriers', 'PoolLib carriers, Master/Checkpoint/Registry/Entry carrier maps', ['LIB_Carriers']),
 ('LIB_PoolRegistry', 'validatePolicy, registry/entry decoders (for 234)', ['LIB_PoolCarriers']),
 ('LIB_PoolAccounts', 'decodeMaster, decodeCheckpoint (for 233)', ['LIB_PoolCarriers']),
 ('LIB_PoolDecoders', 'decodeRequest, req*, reqNullifier, outputLane (for 242)', ['LIB_PoolCarriers']),
 ('LIB_PoolEffects', 'scanProof, reconstruct, encodeStatement, emitResult (for 242/241)', ['LIB_PoolDecoders','LIB_Env']),
 ('LIB_PoolLib', 'bundle L* and D*; NND_PoolValues.Values L*', ['LIB_PoolRegistry','LIB_PoolAccounts','LIB_PoolEffects','LIB_Deployed']),
 ('LIB_Tx2Auth', 'canonical tx2auth from NMN_064.root; weak w registration; Refines064 forms', ['LIB_ErrorDebug','LIB_Root0','LIB_Env']),
 ('LIB_V2Lib', 'bundle V0*; TAS.lib V0*', ['LIB_Tx2Auth']),
 ('LIB_VCarriers', 'VLib carriers, constructors, reads, codecToV', ['LIB_Carriers']),
 ('LIB_VField', 'qadd, qmul, maskValue, eta, at28', ['LIB_VCarriers']),
 ('LIB_VRecords', 'validatedRecord, decodeK29, payload, state, c1Root', ['LIB_VCarriers']),
 ('LIB_VParse', 'parsePrefix, semanticBytesDom, publicTranscript, begin', ['LIB_VCarriers','LIB_Env']),
 ('LIB_VSemantic', 'semanticRounds, circle, claims, terminalQm31, publicDom, finishInputDom', ['LIB_VField','LIB_VRecords','LIB_VParse']),
 ('LIB_VPrepare', 'filled, expandSemantic, expandValues, wideView, viewSemantic', ['LIB_VCarriers']),
 ('LIB_VTx1A', 'parseShape, canonicalScan, accNew, weightsNew, finish, zeroE29', ['LIB_VCarriers']),
 ('LIB_VTx1B', 'batchMerkle, geometry, queryLoop, checkpoint', ['LIB_VTx1A']),
 ('LIB_VLib', 'bundle VL*; per-field Returns evaluators', ['LIB_VSemantic','LIB_VPrepare','LIB_VTx1B','LIB_ErrorDebug']),
 ('LIB_Prepared', 'P* (blocked by F2/F3)', ['LIB_VLib']),
 ('LIB_S1', 'C* (retarget NMT_R2_ReachLibrary to RSL.TX1_345.S1Lib; F4)', ['LIB_VCarriers']),
 ('LIB_Instances', 'final bundle; rfl checks against TAS_Interfaces and the principal fold statements; axioms', ['LIB_PoolLib','LIB_V2Lib','LIB_VLib','LIB_Prepared','LIB_S1','LIB_Transcribed']),
]
# RSL rev3 (ruling (bq)): F1 and F2 resolved in the specs.
FLAGS['F1']['status'] = 'RESOLVED by RSL rev3 (ruling (bq))'
FLAGS['F1']['resolution'] = ('RSL.Env.reservation : Bool (try_reserve reply; true = Ok) and Spec.tryReserve; '
  'Spec.Functional / Child.Functional required at the gate for filled, accNew, weightsNew, claims (on dom) and tx2auth (on Dom064); '
  'TAS Sig.EnvRep binds env.reservation = true <-> headline reservation = .Ok (). See evidence/rowspec-lead-20261107/RSL_REVISION3.md. '
  'The five fields are no longer blocked by a spec error; they remain to be instantiated (adapter new).')
FLAGS['F2']['status'] = 'RESOLVED by RSL rev3 (ruling (bq))'
FLAGS['F2']['resolution'] = ('RowSpec_087 Domain gains (R4) V.checkValuesDom (slice proof OFF_Y1 OFF_INACTIVE) (new VLib field checkValuesDom := 179 compact_check premise verbatim); '
  'recorded as caller clause RSL3-caller:TX1:094:TX1:087:R4 and discharged in 094 by canonical_scan via TX1_094.R4Discharge / r4_of_scan. '
  'PreparedNew stays blocked by F3 (missing TX1:179 child lemmas, LIB_).')
cnt = collections.Counter(x['status'] for x in F)
bystruct = collections.Counter(x['struct'] for x in F)
out = dict(
  title='LIB0 field map: RSL rev2 library structures -> CLOSED ledger roots (F1/F2 resolved by RSL rev3)',
  target_established=False,
  rsl_revision='be66076856e (RSL rev2, frozen by ruling (bp)(4)); F1/F2 resolved by RSL rev3 (ruling (bq), branch codex/cx-rsl-rev3-20261107)',
  ledger='evidence/ledger25-20261111/NMQ_LEDGER.json.xz (sha256 in NMQ_LEDGER.json.sha256), 582 CLOSED / 17 OPEN',
  frozen_source='4bb3b3f51e16b4525f1d10336e2b0bcbbd775387',
  research_base='3493d38575c',
  counts=dict(total=len(F), by_status=dict(cnt), by_struct=dict(bystruct)),
  fields=F, transcriptions=trans, flags=FLAGS,
  order=[dict(module=m, content=c, after=a) for m, c, a in ORDER],
)
json.dump(out, open(sys.argv[2], 'w'), indent=1, ensure_ascii=False)
print(dict(cnt), dict(bystruct), len(F))
