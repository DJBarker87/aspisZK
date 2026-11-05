from pathlib import Path
import json,lzma,hashlib,re,copy,types,subprocess
E=Path(__file__).resolve().parent;R=E.parents[1];P=E.parent/'slice-d-entry5-20261107'
read=lambda p:json.loads(p.read_text());sha=lambda b:hashlib.sha256(b).hexdigest()
closed=read(E/'NIS_CLOSED.json');delta=read(E/'NIS_LEDGER_DELTA.json')
assert closed['new_composed_rows']==3 and delta['counts_after']['CLOSED']==410
base=json.loads(lzma.decompress((E.parent/'ledger11-20261107/NII_LEDGER.json.xz').read_bytes()));by={r['row']:r for r in base['rows']}
v=(P/'NIJ_NFK_validate.py.txt').read_bytes();n=types.ModuleType('NIS_active_NFK');n.__file__=str(P/'NIJ_NFK_validate.py.txt');exec(compile(v,n.__file__,'exec'),n.__dict__);n.BASE_CREDITS=base['NEZ_credits']
model=(E/'NIS_ActiveSlots.lean').read_bytes();assert sha(model) in read(E/'NIS_L010/receipt.json')['source_hashes'].values()
audit=read(E/'NIS_AUDIT.json');assert audit['status']=='PASS_AX2_NFX'
measured={r['root'] for r in audit['raw_roots']}
assert {'NIJ_ActiveSlots.op29_exact','NIJ_ActiveSlots.op30_exact','NIJ_ActiveSlots.retirement_v1','NIJ_ActiveSlots.retirement_v2'}<=measured
source=subprocess.check_output(['git','show','4bb3b3f51e16b4525f1d10336e2b0bcbbd775387:crates/aspis-statement/src/pool_v1/verifier_registry.rs'],cwd=R,text=True)
prefix=source.split('#[cfg(test)]')[0];assert '#[cfg(' not in prefix and '#[cfg_attr(' not in prefix
packet=''.join(l[1:] for l in (E/'NIS_active.patch').read_text().splitlines(True) if l.startswith('+') and not l.startswith('+++'))
assert not re.search(r'\bstatic\b|Option<fn|stub_verified',packet)
assert 'retirement==u64::MAX||slot<retirement' in packet
new=[];certificates=[];rows=[]
for rid,version,op,pos,neg,child in [('TX2:194','V1','op30','NIS_K046','NIS_K047','TX2:193'),('TX2:196','V2','op29','NIS_K048','NIS_K049','TX2:195')]:
 for a,negative in [(pos,False),(neg,True)]:
  r=read(E/a/'receipt.json');log=lzma.decompress((E/a/'stdout.log.xz').read_bytes()).decode()
  assert r['exit_status']==(1 if negative else 0)
  assert ('VERIFICATION:- FAILED' if negative else 'VERIFICATION:- SUCCESSFUL') in log
  if negative:assert re.search(r'\*\* 1 of \d+ failed',log) and 'unwinding assertion' not in log
  assert 'timed out' not in log.lower()
  assert read(E/(a+'-graph-check.json'))['graph_matches_frozen'] and read(E/(a+'-erasure-check.json'))['passed'] and read(E/(a+'-lock-check.json'))['unchanged']
  assert read(E/(a+'-isolation.json'))['allowed'] is True
  assert r['env']['CARGO_TARGET_DIR']==r['native_command'][r['native_command'].index('--target-dir')+1]
  assert r['source_hashes']['NIJ_src/crates/aspis-statement/src/pool_v1/NIS_active.rs']==sha(packet.encode())
 region=prefix.split('impl VerifierRegistryEntry'+version+' {',1)[1].split('\n}',1)[0]
 assert 'self.status == VerifierEntryStatusV1::Active' in region and 'self.activation_slot <= slot' in region and 'self.has_no_retirement_slot() || slot < self.retirement_slot' in region
 assert 'self.retirement_slot == POOL_V1_VERIFIER_ENTRY_NO_RETIREMENT_SLOT' in region
 row=copy.deepcopy(by[rid]);claim='NIS::active_'+version.lower()
 assert row['composed_status']=='OPEN' and not row['named_hypotheses']
 childclaim='NHY::retirement_'+version.lower()
 inherited=read(E.parent/'slice-d-entry4-20261106/NHY_LEDGER_DELTA.json')
 assert next(r for r in inherited['rows'] if r['row']==child)['composed_status']=='CLOSED'
 for o in row['caller_domain_obligations']:
  same=('VerifierRegistryEntry'+version+'::') in o['callee']
  o.update(status='CLOSED',callee_local_status='CLOSED' if same else 'EXCLUDED-TYPED-ALTERNATIVE',callee_claims=[childclaim] if same else [],discharged_by=claim+(': SAME arbitrary typed shared record enters the actual helper; native whole active method executes it; NIJ_ActiveSlots.retirement_'+version.lower()+' proves the natural source-call structure, domain every record/u64 slot.' if same else ': Opposite-version receiver is excluded by frozen inherent method typing; no callee claim selected.'))
 c=dict(id=claim,subject=row['function'],route='y: NEW deployed native whole-body scalar packet, local state/no writable static; canonical cohort equality',model_theorem='NIJ_ActiveSlots.'+op+'_exact',root_domain='Every valid typed '+version+' record, every u64 slot; exhaustive four status constructors; all other fields arbitrary. No successful status/slot/validator precondition.',inner_hypotheses_remaining=[],native_passes=[pos],matched_controls=[neg],callee_laws=[childclaim],source_association='NIS_active.patch directly invokes actual frozen is_active_at and has_no_retirement_slot. Full deployed features/offline graph/frozen lock/KMX/isolation checks. Pure no-cfg source and u64::MAX constant pinned. NIS_ActiveSlots is import-only retarget, natural four-status/U64 predicate and typed helper composition audited in same canonical/headline closure. Suspended NCF_K002/006 NEVER selected or restored.',effects='Immutable typed shared reference and Bool; no allocation/account mutation/runtime syscall/function-pointer dispatch in reached actual method.',combined='NIS_L025',audit=['NIS_L032 all79 raw roots standard','NIS_L033 NFX zero defects'],trust_reclassification='Retained P6/D188 option-A/native/compiler/ABI trust; no new runtime item.',root_model='AspisR1.RPx_Deployed.deployed; frozen3; L154 parameter')
 c['semantic_review_sha256']=sha(json.dumps(c,sort_keys=True).encode())
 row.update(composed_status='CLOSED',bridge_status='CLOSED-CONDITIONAL',selected_claims=[claim],open_transitive_dependencies=[],active_support_receipts=[str((E/pos/'receipt.json').relative_to(R))],composed_reason='New K-3-clean deployed active-at packet and matched inverse assertion; same typed helper/domain, canonical natural/cohort law and clean full composition audit.')
 assert not n.row_checks(row,by[rid],c),n.row_checks(row,by[rid],c)
 n.certificate_checks(type('Support',(),{'support':lambda self,c:None})(),c)
 small=copy.deepcopy(base);small['rows']=[by[rid]]
 admitted=n.admit(small,{rid:('NIS',row)},{rid:c},{'NIS':[rid]});assert admitted['rows'][0]['composed_status']=='CLOSED'
 bad=copy.deepcopy(row);bad['active_support_receipts']=['evidence/native-u04d-20261028/'+('NCF_K006' if version=='V1' else 'NCF_K002')+'/receipt.json']
 assert 'NEZ K-2/K-3 active support denial' in n.row_checks(bad,by[rid],c)
 new.append(rid);certificates.append(c);rows.append(admitted['rows'][0])
closed.update(new_composed_rows=5,new_composed_functions=4);closed['functions']+=certificates
delta['new_closed_rows']+=new;delta['rows']+=rows;delta['counts_after']={'CLOSED':412,'QUALIFIED':0,'OPEN':187}
delta['active_denial_control']='Replacing either new receipt with suspended NCF_K002/006 is still rejected by unchanged NFK.'
(E/'NIS_CLOSED.json').write_text(json.dumps(closed,indent=1)+'\n');(E/'NIS_LEDGER_DELTA.json').write_text(json.dumps(delta,indent=1)+'\n')
(E/'NIS_ACTIVE_ASSOCIATION.json').write_text(json.dumps(dict(status='PASS_NEW_NATIVE_NO_SUSPENDED_REUSE',new_rows=new,source_sha256=sha(source.encode()),packet_sha256=sha(packet.encode()),raw_model_sha256=sha(model),zero_writable_statics=True,old_controls_remain_suspended=True),indent=1)+'\n')
print(json.dumps(dict(status='PASS',new_rows=new,counts=delta['counts_after'])))
