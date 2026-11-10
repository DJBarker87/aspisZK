import json,pathlib
E=pathlib.Path(__file__).resolve().parent
old=json.load(open(E/'../prov-p3o-20261110/PCVO_UNRELATED.json'))['items']
cov={
 ('caller','op3'):['AspisR1.PCVP_NocSlots.op3','NOC_ConvLeaves.parse (converse)'],
 ('caller','op4'):['AspisR1.PCVP_NocSlots.op4','NOC_Conv094.scan (converse)'],
 ('caller','op5'):['AspisR1.PCVP_NocSlots.op5','NOC_ConvLeaves.view (converse)'],
 ('caller','op6'):['NOC_Tx1Forward.batch (forward, stated at NOC cur c)','NOC_Tx1Conv (converse inside tx1)'],
 ('caller','op7'):['AspisR1.PCVP_NocSlots.op7 (to native query body only)','NOC_Tx1Forward.query (forward to LIBC_QueryLoop)'],
 ('caller','op8'):['AspisR1.PCVP_NocSlots2.op8','NOC_ConvLeaves.prepared (converse)'],
 ('caller','op9'):['NOC_SeedTransfer.op9 / NOC_Op9.op9 (forward, at NOC)','NOC_SemConv (converse)'],
 ('caller','op10'):['AspisR1.PCVP_NocSlots2.op10','NOC_ConvLeaves.expand_semantic'],
 ('caller','op11'):['NOC_PrepareFront.values (installed expandValues = LIBC_ExpandValuesModel.output; used as expV in NOC_PrepareFront.source)','NOC_ConvLeaves.expand_values'],
 ('caller','op16'):['AspisR1.PCVP_NocSlots.op16'],
 ('caller','op17'):['AspisR1.PCVP_NocSlots.op17'],
 ('caller','op18'):['AspisR1.PCVP_NocSlots2.op18','NOC_Conv094.weightsNew (converse)'],
 ('caller','op19'):['AspisR1.PCVP_NocSlots.op19','NOC_Conv094.geometry (converse)'],
 ('caller','op20'):['AspisR1.PCVP_NocSlots.op20','NOC_Conv094.accNew (converse)'],
 ('caller','op1'):['AspisR1.PCVP_C.noc_op1 / noc_op1_filled / noc_op1_ne_div (corrected seed; supersedes the PCVO divergent-op1 entry)','NOC_PrepareFront.filled','NOC_ConvLeaves.filled (converse)'],
 ('stage1','op21'):['whole-function only: NOC_Stage1Iff.iff345 and AspisR1.PCVP_S1Compose.fresh_stage1_iff (not a per-slot theorem)'],
 ('stage1','op24'):['whole-function only: NOC_Stage1Iff.iff345 and AspisR1.PCVP_S1Compose.fresh_stage1_iff'],
 ('stage1','op47'):['whole-function only: NOC_Stage1Iff.iff345 and AspisR1.PCVP_S1Compose.fresh_stage1_iff'],
}
items=[]
nrel=0
for it in old:
    it=dict(it)
    if it['classification']=='DEPLOYED_SLOT_NOT_RELATED_TO_FROZEN_EMISSION' or it['deployed_slot']=='op1':
        k=(it['file'],it['deployed_slot'])
        it['library_model_correspondence_at_corrected_seed']=cov.get(k,[])
        it['relation_to_frozen_emission_of_callee']='NOT PROVED (needs the callee gate-definition status; this job did extraction 0)'
        if cov.get(k): nrel+=1
        elif it['file']=='stage2': it['stage2_note']='no per-slot correspondence located or proved here; stage2/tx2 coverage in evidence/tx2-owned-20261111 and tx2-auth-20261111 and PCVN_ was not inspected by this job'
    items.append(it)
json.dump(dict(schema='PCVP_UNRELATED/1',target_established=False,
 note='Updated from PCVO_UNRELATED.json. library_model_correspondence_at_corrected_seed = existing or newly restated theorem relating the installed slot to the LIBRARY MODEL (LIB_/LIBC_) on the reached domain named in the theorem. None of these relates a slot to the frozen 4bb3b3f emission of the callee; that is the gate-definition (PCXD) status, unchanged. Every deployed-slot Bound field remains organisation, not discharge.',
 slots_with_library_model_correspondence=nrel,items=items),open(E/'PCVP_UNRELATED.json','w'),indent=1)
status=dict(schema='PCVP_STATUS/1',target_established=False,frozen_source='4bb3b3f51e16b4525f1d10336e2b0bcbbd775387',closure='codex-cx-replay-l187-20261109/objs (by reference)',
 corrected_seed='AspisR1.NOC_HostCtx.sdk c / NOC_HostSeed.m0 (op1 = NOC_HostSeed.filled reserved; sdk op10 differs from NNH seed). P3o deployed_prepare/deployed_tx1 at NNH_HostSeed.m0 are NOT credited (op1 diverges there; PCVP_C.old_op1_div).',
 claims=[
 dict(id='C1',file='PRVEq_CallerPrepTx1DeployedNOC_o1.lean',scope='PCVP_L003',theorems=['noc_prepare','noc_tx1','seed_prepare','noc_op1','noc_op1_filled','noc_op1_ne_div','old_op1_div'],
  statement='fresh frozen PCVK_C prepare/tx1 at xOf(currentInstalled(NOC_HostCtx.configuration c)) = gate prepare/tx1 at that Ops, for every host context c; seed-generic over the Uninstalled seed (seed_prepare). Non-vacuity: installed op1 = NOC_HostSeed.filled reserved, returns Ok(zeros n) on a granted reservation (NOC_PrepareFront.filled, cited) so not Result.div; old seed op1 is div.',
  status='VERIFIED_CONDITIONAL_ON_BINDING (Bound callee fields instantiated from the Ops by rfl: organisation, not discharge)'),
 dict(id='C2',file='PRVEq_AdapterStage1DeployedNOC_o1.lean / PRVEq_AdapterStage2DeployedNOC_o1.lean',scope='PCVP_L005, PCVP_L007',theorems=['PCVP_S1.noc_model1','PCVP_S2.noc_model2'],
  statement='fresh frozen stage1_owned/stage2_owned at xOf(NOC_HostCtx.sdk c) = NOC_HostCtx.model1 c / model2 c (stage2 with hashv := LIB_Env.hashv (envOf c); NOC_HostCtx.hashv c = DGP_HostDigest.hashvInst c.sha256 is not identified with it here).',
  status='VERIFIED_CONDITIONAL_ON_BINDING'),
 dict(id='C3',file='PRVEq_NocCallerSlots_o1.lean, PRVEq_NocCallerSlots2_o1.lean',scope='PCVP_L009, PCVP_L010',theorems=['PCVP_NocSlots.cur_eq,op3,op4,op5,op7,op16,op17,op19,op20','PCVP_NocSlots2.op8,op10,op18'],
  statement='existing installed-op = library-model theorems restated at the corrected seed (curN c; m := NOC_HostSeed.m0, defeq checked in PCVP_L008). Re-statements of NNV_/NNH_ theorems, no new mathematics. L010 also prints axioms of 17 cited NOC_ theorems (all standard).',
  status='VERIFIED (relation to library model only)'),
 dict(id='C4',file='PRVEq_NocStage1Compose_o1.lean',scope='PCVP_L011',theorems=['PCVP_S1Compose.fresh_stage1_iff'],
  statement='fresh frozen stage1_owned at the headline sdk Ok-iff library tx1Value (composition of C2 with NOC_Stage1Iff.iff345), no domain hypothesis.',status='VERIFIED_CONDITIONAL_ON_BINDING'),
 dict(id='C5',file='PRVEq_NocPrepTx1Compose_o1.lean',scope='PCVP_L013',theorems=['PCVP_CComp.fresh_prepare_forward','fresh_prepare_converse','fresh_tx1_forward','fresh_tx1_converse'],
  statement='the existing NOC_PrepareFront/NOC_PrepareConv/NOC_Tx1Forward/NOC_Tx1Conv theorems (stated at cur c) hold for the fresh frozen prepare/tx1 via C1.',status='VERIFIED_CONDITIONAL_ON_BINDING'),
 ],
 scopes=dict(lean='L001-L013 (13 of 45), extraction 0',peak_rss_kib_max=6808172,failed=['PCVP_L002 (type mismatch: noc_op1 stated as (curN c).op1 with implicit args; fixed by stating @Ops.op1 form; receipt directory was removed by the worker, the failure is in PCVP_ATTEMPTS.jsonl)']),
 no_difference_at_matching_configuration=True)
json.dump(status,open(E/'PCVP_STATUS.json','w'),indent=1)
json.dump(dict(schema='PCVP_REMAINING/1',target_established=False,items=[
 'stage2 adapter slots op22,op23,op20,op16,op17,op11,op50,op52,op49,op48,op51,op45,op53,op44: no per-slot library-model correspondence or frozen-emission relation proved here',
 'op21/op24/op47 (stage1): only the whole-function Ok-iff (NOC_Stage1Iff.iff345), no per-slot theorem',
 'every caller slot: relation of the library model to the FROZEN emission of the callee is the PCXD gate status (OPEN/HAND_ADAPTED/RECEIPTED); unchanged; needs fresh 4bb3b3f extraction (budget 0 here)',
 'DEPENDS_ON_LIBRARY_TRUST (17) and the 22 gate-definition fields: unchanged from PCVO_UNRELATED.json',
 'NOC_HostCtx.hashv c vs LIB_Env.hashv (envOf c) identification for noc_model2',
 'a further host re-instantiation at NPO_ program ids: C1 is seed-generic in the six constant fields (rfl) so should transfer; not run'],
 next_deliverable='fresh 4bb3b3f extractions (extraction budget) of the callees whose gate status is open, then equalities against the library models already proved here'),open(E/'PCVP_REMAINING.json','w'),indent=1)
json.dump(dict(schema='PCVP_TOOLS/1',tools=[
 dict(file='PCVP_run.py',from_='prov-p3o-20261110/PCVO_run.py',changes='PCVO->PCVP, p3o->p3p, host workspace codex-pc-prov-p3p-20261110; admission unchanged (host<6, Stream C<2, disk>=40GB, reservation barrier)'),
 dict(file='PCVP_run_host.py',from_='PCVO_run_host.py',changes='rename only'),
 dict(file='PCVP_go.sh',from_='PCVO_go.sh',changes='rename only'),
 dict(file='PCVP_next.sh',from_='new',changes='picks next free PCVP_Lnnn from PCVP_ATTEMPTS.jsonl and runs one scope'),
 dict(file='PCVP_gen1.sh / PCVP_gen2.sh',from_='new',changes='generate the *DeployedNOC_o1 files from the P3o deployed files plus corrected-seed sections'),
 dict(file='findmods.sh',from_='prov-p3o-20261110/findmods.sh',changes='none')]),open(E/'PCVP_TOOLS.json','w'),indent=1)
json.dump(dict(schema='PCVP_CLASSIFICATIONS/1',items=[
 dict(case='op1 non-vacuity: NOC_PrepareFront.filled cited rather than re-proved',classification='cite-first (brief)',reason='existing theorem at the NOC cur c'),
 dict(case='stage2 slots with no gate definition named',classification='UNRELATED/REMAINING',reason='frozen-emission relation needs extraction (budget 0); library-model coverage not located'),
 dict(case='old receipt directory PCVP_L002 removed',classification='process slip, recorded',reason='failed elaboration scope; failure retained in PCVP_ATTEMPTS.jsonl')]),open(E/'PCVP_CLASSIFICATIONS.json','w'),indent=1)
