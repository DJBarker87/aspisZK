from pathlib import Path
import json
E=Path(__file__).resolve().parent
rows=json.loads(Path('evidence/native-tx2d-20261027/NBH_MEMBER_STATUS.json').read_text())
for r in rows:
 name=r['id'].split('::')[-1];new=''
 if name=='encode_pool_v1_pair_verified_afterstate_v1':
  new='NBK_AfterstateResult.source gives full emitted Result for all typed records, reusing NBH validator and S2K exact bytes. NBK K001-K020 check all20 fixed native row stores with arbitrary bytes and full frame (only count gates whose receipts pass). K059 is the native fixed prefix, with explicit SAME-root encoded-byte cut. OPEN: NBK_Dep_DigestEncode plus complete native call/iterator/prefix association; byte-cut parameters are not child successes.'
 elif name=='encode_pool_v1_pair_live_snapshot_v1':
  new='NBK_LiveResult.source gives full emitted status, all bytes and unchanged rejection output for every snapshot/output length; NBK_LiveStep/LiveBytes prove the actual model loop by induction and NBK_LiveFrame.byte its frame. K021-K040 are20 fixed native row stores; K060 fixed header/fill (use only passing receipts). OPEN: SAME-root/row NBK_Dep_DigestEncode, native iterator/header/domain composition, complete native Result association. WrongLength still precedes validation/mutation.'
 elif name=='encode_pool_v1_pair_late_public_statement_v1':
  new='NBH K028 preflight retained unchanged; NBK_LatePreflight proves exact emitted WrongLength/AfterstateIndexMismatch with unchanged output, including Option checked-add mismatch.  complete emitted live and afterstate Result laws now available as NBK_LiveResult.source/NBK_AfterstateResult.source. OPEN: native late fill/header, SAME native live/afterstate child bridges, exact subrange/return-state/error composition. ASF8 live child width1520 is checked separately; do not assume a successful child.'
 elif name in ['decode_pool_v1_pair_forest_master_v1','decode_pool_v1_pair_forest_checkpoint_v1']:
  new='NBK K043-K050 (master) / K051-K058 (checkpoint) specialize one native decoder iteration per lane, arbitrary source bytes and prior8-row state; exact little-endian word, full other-row frame, and checkpoint capacity rejection. OPEN: association/induction on the SAME adopted op48/49 carriers, reserved scans and remaining NBH-listed children/validation/error maps. NBK_DeployedCallbackSelection.policy_accounts proves actual SDK selects input adapter slots; it supplies no decoder correspondence.'
 elif name=='validate_pool_v1_pair_forest_terminal_statement_v1':
  new='NBK_StatementPrefix.zero_rejected/lane_rejected prove exact emitted early errors on SAME common record; K041 projected native prefix; K042 exact ASF8 child widths/typed addresses and deployment-domain location public256..288 (use only passing receipts). OPEN: good-prefix continuation, SAME variant PaymentEncode, ordered pool/domain/checkpoint/anchor bindings, output-lane and late Encode bridges, and complete native/cohort association. No caller success is assumed.'
 elif name=='encode_pool_v1_pair_forest_terminal_statement_v1':
  new='NBH K029 fixed prefix retained; NBK K042 checks exact late1520/payment216 ranges and live deployment public256..288. NBK model early validator laws do not establish encoder success. OPEN: SAME whole validator, DigestEncode, complete late child/payment encoder and complete native/cohort byte/error composition.'
 elif r['unit']=='U04' and r['status'].startswith('OPEN'):
  new='NBK_DeployedCallbackSelection.registry/policy_accounts audit the coherent SDK: op25/26 V1 paused/immutable, op27/28 V2 paused/immutable, op29/30 active V2/V1, op31-34 decoders, op15 policy, op48/49 account decoders are retained from input adapter. No new dictionary is installed and no arbitrary callback value is equated to native execution. Retain exact NBH native domains; SAME-carrier association remains OPEN.'
 if new:r['NBK_progress_or_open']=new
(E/'NBK_MEMBER_STATUS.json').write_text(json.dumps(rows,indent=2)+'\n')
for unit in ['U03','U04','U05']:
 selected=[r for r in rows if r['unit']==unit];opened=[r for r in selected if r['status'].startswith('OPEN')]
 text=f'# NBK {unit}: OPEN\n\n{len(selected)-len(opened)}/{len(selected)} members CLOSED by inherited NBD/NBH evidence; {len(opened)} exact OPEN members. New fragment/model work is not counted as whole-member closure. No headline premise removed; deployed target not established. Native gate references apply only if receipt exit0 and frozen graph/lock checks pass.\n\n'
 text+='| Frozen member | Status | Evidence and exact remaining obligation |\n|---|---|---|\n'
 for r in selected:
  detail=r['evidence_or_open']+' '+r.get('NBK_progress_or_open','')
  text+=f'| `{r["id"]}` | {r["status"]} | {detail} |\n'
 text+='\nRetained: frozen3, RuntimePersistence, approved game, L154 statement parameter, narrowed D188, P6/TrustedStd/runtime and source-to-ELF boundaries. No native bridge is inherited from LPb’s drifted standalone lock. NBG lower work is not merged into this branch and no lower closure is assumed. ASR8 emission/results remain optional to headline soundness because op53 is universal.\n'
 (E/f'NBK_{unit}_BRIDGE.md').write_text(text)
