"""Strict local evidence validator; model/local facts cannot promote Pool rows."""
from pathlib import Path
import json,hashlib,re,copy,sys
E=Path(__file__).resolve().parent
ALLOWED={'propext','Classical.choice','Quot.sound'}
PAIRS=[(n,n+1) for start,end in [(2,20),(26,40),(46,70),(75,93),(95,101),(103,117)] for n in range(start,end+1,2)]
EXPECTED_TIMEOUT={24,25,44,45,73,74,119,120};EXPECTED_REJECT={1,22,23,42,43,72}
CURRENT={'NIO_Cpi':6,'NIO_Infos':7,'NIO_Nested':8,'NIO_Windows':9,'NIO_AbortScopes':10,'NIO_LoopModel':11,'NIO_Invariant':12,'NIO_COMBINED_IMPORT':13,'NIO_Driver':14,'NIO_ProofDriver':15}
def read(p):return json.loads(p.read_text())
def check(s):
 assert len(s['native'])==120 and set(s['native'])==set(range(1,121))
 for n,row in s['native'].items():
  assert row['graph'] and row['exact_graph'] and row['lock'] and row['source'] and row['rule16']
  assert row['offline'] and row['optimized'] and row['copy_pin'] and row['feature_parity']
  assert row['limits']=={'memory.high':'6442450944','memory.max':'8589934592','memory.swap.max':'0','pids.max':'64'}
  assert row['fields_complete']
 for p,c in PAIRS:assert s['native'][p]['verdict']=='PASS' and s['native'][c]['verdict']=='FAIL'
 for n in EXPECTED_TIMEOUT:assert s['native'][n]['verdict']=='TIMEOUT'
 for n in EXPECTED_REJECT:assert s['native'][n]['verdict']=='REJECT'
 assert len(PAIRS)==53
 assert len(s['raw'])==37 and all(set(r['walked_axioms'])<=ALLOWED for r in s['raw'])
 assert s['fixtures']==8 and s['scan_exit']==0 and not any(s['scan_defects'])
 assert s['source_freeze']==0 and s['current_sources_match']
 assert s['closed_functions']==0 and s['closed_pool_rows']==[] and s['promotions']==[]
 assert s['cpi_status']==['OPEN']*4 and not s['pending_trust_used'] and not s['source_scope_instantiated']
 assert s['event_count']==353 and s['source_event_status']=={'OPEN'}
 assert s['no_large_files'] and s['no_committed_binary']
 return True
native={}
for n in range(1,121):
 a=f'NIO_K{n:03d}';r=read(E/a/'receipt.json');cfg=read(E/(a+'.json'));text=(E/a/'stdout.log').read_text()
 verdict='TIMEOUT' if 'timed out' in text else 'PASS' if 'VERIFICATION:- SUCCESSFUL' in text else 'FAIL' if 'VERIFICATION:- FAILED' in text else 'REJECT'
 graph=read(E/(a+'-graph-check.json'));lock=read(E/(a+'-lock-check.json'));src=read(E/(a+'-source-check.json'));rules=read(E/(a+'-rule16-check.json'));features=read(E/(a+'-metadata-pin.json'))
 native[n]=dict(verdict=verdict,graph=graph['graph_matches_frozen'],exact_graph=graph['exact_LPm_graph'],lock=lock['unchanged'] and lock['before']==lock['after']=='5782e6a32026fdd95d252d0db7ea20b16716e6deb4f5a397e744886bb6ba22ef',source=not src['errors'],rule16=rules['no_writable_static'],offline=cfg['env']['CARGO_NET_OFFLINE']=='true',optimized=cfg['env']['CARGO_PROFILE_DEV_OPT_LEVEL']=='3',copy_pin=cfg['copy_patch_sha256']=='bcdf749b78eb6143789500d98d64ec3d407b8a17a6d1290c70c822473e8e9a67',feature_parity={'r1-split-checkpoint','pair-forest-source-invariant-audit','pair-forest-source-result-invariant-audit'}<=set(next(x['features'] for x in features['features_all_crates'] if x['name']=='aspis-pool')),limits=r['limits'],fields_complete=all(r.get(k) is not None for k in ['module','exit_status','wall_seconds','peak_rss_kib','swaps','source_revision','source_hashes']))
raw=read(E/'NIO_audit/batch0/proof0.json')['results'];scan=[json.loads(l) for l in (E/'NIO_LOADED_scan.jsonl').read_text().splitlines()]
closed=read(E/'NIO_CLOSED.json');delta=read(E/'NIO_LEDGER_DELTA.json');audit=read(E/'NIO_AUDIT.json');opens=read(E/'NIO_OPEN_SITES.json')['events']
matching=True
for module,n in CURRENT.items():
 snapshot=E/f'NIO_L{n:03d}'/'sources'/'NIO_generated'/(module+'.lean')
 matching &= snapshot.read_bytes()==(E/(module+'.lean')).read_bytes()
 matching &= read(E/f'NIO_L{n:03d}'/'receipt.json')['exit_status']==0
large=[str(p) for p in E.rglob('*') if p.is_file() and p.stat().st_size>20*1024*1024]
binaries=[str(p) for p in E.rglob('*') if p.is_file() and p.suffix in ['.olean','.o','.a','.so','.dylib','.exe','.bin']]
snapshot=dict(native=native,raw=raw,fixtures=len(read(E/'NIO_audit/fixtures/fixtures.json')['results']),scan_exit=read(E/'NIO_audit/scan/scan.json')['exit_status'],scan_defects=[sum(len(r['dangling']) for r in scan),sum(len(r['duplicate_owners']) for r in scan),sum(not r['imports_match'] for r in scan)],source_freeze=read(E/'NIO_SOURCE_FREEZE.json')['tracked_crates_programs_diff_exit'],current_sources_match=matching,closed_functions=closed['complete_source_functions'],closed_pool_rows=closed['closed_pool_consumers'],promotions=delta['promote_to_closed'],cpi_status=[r['status'] for r in read(E/'NIO_CPI_GUARDS.json')],pending_trust_used=audit['pending_runtime_trust_used'],source_scope_instantiated=closed['source_scope_run_instantiated'],event_count=len(opens),source_event_status={x['status'] for x in opens},no_large_files=not large,no_committed_binary=not binaries)
check(snapshot)
mutations=[]
def reject(name,change):
 s=copy.deepcopy(snapshot);change(s)
 try:check(s)
 except AssertionError:mutations.append(dict(name=name,rejected=True));return
 raise AssertionError('Validator accepted mutation '+name)
reject('passing check relabelled after timeout',lambda s:s['native'][2].update(verdict='TIMEOUT'))
reject('matched control spuriously passes',lambda s:s['native'][3].update(verdict='PASS'))
reject('drifted dependency graph',lambda s:s['native'][2].update(graph=False))
reject('lock drift',lambda s:s['native'][2].update(lock=False))
reject('unfrozen source',lambda s:s['native'][2].update(source=False))
reject('wrong deployed features',lambda s:s['native'][2].update(feature_parity=False))
reject('copy patch changed',lambda s:s['native'][2].update(copy_pin=False))
reject('writable static',lambda s:s['native'][2].update(rule16=False))
reject('uncapped scope',lambda s:s['native'][2].update(limits={}))
reject('nonstandard raw axiom',lambda s:s['raw'][0].update(walked_axioms=['sorryAx']))
reject('missing fixture evidence',lambda s:s.update(fixtures=0))
reject('incompatible owner',lambda s:s.update(scan_defects=[0,1,0]))
reject('stale source snapshot',lambda s:s.update(current_sources_match=False))
reject('model promoted to source owner',lambda s:s.update(closed_functions=1))
reject('unauthorized Pool promotion',lambda s:s.update(promotions=['Pool:new']))
reject('pending runtime trust assumed',lambda s:s.update(pending_trust_used=True))
reject('conditional ScopeRun claimed instantiated',lambda s:s.update(source_scope_instantiated=True))
reject('CPI site closed without packet',lambda s:s.update(cpi_status=['CLOSED']*4))
reject('remaining event omitted',lambda s:s.update(event_count=352))
reject('oversized evidence',lambda s:s.update(no_large_files=False))
reject('committed binary',lambda s:s.update(no_committed_binary=False))
report=dict(exit=0,kani=120,matched_pairs=len(PAIRS),current_source_modules=len(CURRENT),raw_roots=len(raw),standard_axioms_only=True,source_events=len(opens),pool_promotions=0,mutation_controls=mutations,large_files=large,binaries=binaries)
(E/'NIO_VALIDATION.json').write_text(json.dumps(report,indent=2)+'\n')
print('NIO evidence validation PASS; '+str(len(mutations))+' misleading-evidence mutations rejected')
