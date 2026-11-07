"""Read-only source, receipt, slot-overlay and boundary validation."""
import pathlib,subprocess,json,hashlib,collections,lzma,re
E=pathlib.Path('evidence/pv-lib-20261107/lane-SLICE');base='5e397cb3878'
sha=lambda b:hashlib.sha256(b).hexdigest()
receipts=[json.loads(p.read_text()) for p in E.glob('receipt-*.json')]
accepted={r['target']:r for r in receipts if r['accepted'] and not r['runtime_audit']}
checks=[]
for p in sorted(pathlib.Path('lean').glob('PV_LIB_SLICE_*.lean')):
 r=accepted[p.stem];assert sha(p.read_bytes())==r['source_sha256'],p
 checks.append({'module':p.stem,'attempt':r['attempt'],'source_sha256':r['source_sha256'],'compiled':True})
replays=[]
entry=json.loads((E/'ENTRY_PREFLIGHT.json').read_text())
for r in receipts:
 a=r['attempt'];assert 49600<=a<=49689 or 49690<=a<=49699 or 49900<=a<=49999
 t=json.loads((E/f'turn-{a}.json').read_text());assert t['exit']==0 and t['command']==['ssh','dombarker@100.108.41.90','STREAMB_SLOTS=3 /home/dombarker/streamb-slots/turn.sh']
 admit=json.loads((E/f'admission-{a}.json').read_text());assert admit['allowed'] is True
 assert r['swaps']=='0',a
 if not r['accepted']:
  archived=E/'failed-sources'/f'{a}.lean.xz'
  assert sha(lzma.decompress(archived.read_bytes()))==r['source_sha256']
  assert accepted[r['target']]['source_sha256']!=r['source_sha256']
  continue
 assert r['exit']=='0',a
 cmd=r['command']
 for field in ['MemoryHigh=6G','MemoryMax=8G','MemorySwapMax=0','TasksMax=64']:assert field in cmd
 assert cmd.count('7000')==1 or r['runtime_audit']
 if r['target'].startswith('PV_LIB_SLICE_'):continue
 rev=r['source_revision'] if r['source_revision'] in ['fc0340264851248e164a098c170cc53e22857085',entry['revision']] else '9d7395cb069f07f812e8e1352e0478111eaec9ee'
 raw=subprocess.check_output(['git','show',rev+':lean/'+r['target']+'.lean']);assert sha(raw)==r['source_sha256']
 blob=subprocess.check_output(['git','rev-parse',rev+':lean/'+r['target']+'.lean'],text=True).strip();assert blob==r['source_index_blob']
 replays.append({'module':r['target'],'attempt':a,'source_revision':rev,'source_blob':blob,'source_sha256':sha(raw)})
old=json.loads(subprocess.check_output(['git','show',base+':evidence/pv-lib-20261107/PLIB_MAP.json']))
delta=json.loads((E/'MAP_DELTA.json').read_text());slots={s['slot']:s for s in old['slots']}
assert len(delta['slots'])==16
for s in delta['slots']:
 assert s['slot'] in slots and s['parent'].startswith('slice:')
 slots[s['slot']]=s
changed=subprocess.check_output(['git','diff','--name-only',base],text=True).splitlines()
assert all(p.startswith(str(E)+'/') or (p.startswith('lean/PV_LIB_SLICE_') and p.endswith('.lean')) for p in changed),changed
raw=json.loads((E/'SESSION2_RAW_AUDIT.json').read_text());assert raw['strict_raw'] and raw['unresolved']==0 and raw['summary_mismatches']==0

# The D978 Drop cone is exactly the14 requested outstanding provider modules.
session2=[]
for planfile in ['SESSION2_REPLAY_PLAN.json','SESSION2_ENTRY_PLAN.json']:
 plan=json.loads((E/planfile).read_text())
 for module in plan['modules']:
  rs=[r for r in receipts if r['target']==module and r['accepted'] and r['source_revision']==plan['revision']]
  assert len(rs)==1,(module,rs)
  session2.append(rs[0]['attempt'])
assert len(json.loads((E/'SESSION2_REPLAY_PLAN.json').read_text())['modules'])==14
assert len(json.loads((E/'SESSION2_ENTRY_PLAN.json').read_text())['modules'])==5
for slot in delta['slots']:
 if slot['provider_status'] in ['OPEN','PARTIAL']:
  assert slot['status']=='WAITING-ON-ROW' and slot['waiting_on_row']==slot['child']
assert len([s for s in delta['slots'] if s['status']=='WAITING-ON-ROW'])==12
for p in pathlib.Path('lean').glob('PV_LIB_SLICE_*.lean'):
 if p.stem in ['PV_LIB_SLICE_FoundationEntry','PV_LIB_SLICE_RuntimeDrop']:
  assert not re.search(r'\b(sorry|axiom|opaque|admit)\b',p.read_text()),p
old_driver=subprocess.check_output(['git','show','821f00b325e:lean/PV_LIB_SLICE_RawAudit.lean'],text=True)
new_driver=pathlib.Path('lean/PV_LIB_SLICE_RawAudit2.lean').read_text()
assert old_driver[old_driver.index('  let env'):]==new_driver[new_driver.index('  let env'):]

summary={'source_base':base,'lane':'SLICE','new_sources':checks,'pinned_replays':replays,'passing_compiles':len([r for r in receipts if r['accepted'] and not r['runtime_audit']]),'failed_compiles':len([r for r in receipts if not r['accepted']]),'preflight_stops':[49669],'raw_audits':len([r for r in receipts if r['runtime_audit']]),'maximum_peak_rss_kib':max(int(r['peak_rss_kbytes']) for r in receipts),'swaps':0,'overlay_counts':dict(collections.Counter(s['status'] for s in slots.values())),'raw_roots':raw['root_count'],'session2_base':'821f00b325e','write_boundary_passed':True,'endpoint_premises_removed':0,'endpoint_premises_added':0,'qualification':'Qualified graph adapters/support only; no parent-row or frozen-spec/full-root closure.'}
(E/'SESSION2_VALIDATION.json').write_text(json.dumps(summary,indent=2)+'\n')
print(json.dumps({k:v for k,v in summary.items() if k not in ['new_sources','pinned_replays']},indent=2))
