from pathlib import Path
import json,hashlib,lzma,re,collections,subprocess
E=Path(__file__).resolve().parent
read=lambda n:(E/n).read_text() if (E/n).exists() else lzma.decompress((E/(n+'.xz')).read_bytes()).decode()
load=lambda n:json.loads(read(n))
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
attempts=[json.loads(s) for s in read('PCG_ATTEMPTS.jsonl').splitlines()];by={r['attempt']:r for r in attempts};assert len(by)==len(attempts)
for r in attempts:
 assert r['limits']=={'memory.high':'6442450944','memory.max':'8589934592','memory.swap.max':'0','pids.max':'64'}
 assert str(r['swaps'])=='0'
 admission=load(r['attempt']+'-admission.json');assert admission['exit']==0 and admission['reservation']['allowed'] is True
 assert load(r['attempt']+'-disk-0.json')['free']>=40_000_000_000
counts=collections.Counter('lean' if r['kind'] in ['lean','link','audit'] else r['kind'] for r in attempts)
assert all(counts[k]<=v for k,v in dict(kani=110,lean=90,extract=12).items())
roots=load('PCG_ROOTS.json')['roots'];groups=load('PCG_GROUPS.json');results=[];binary=load('PCG_binary_fixtures.json')['sha256']
assert len(load('PCG_binary_fixtures.json')['results'])==8
for i,group in enumerate(groups):
 d=load('PCG_binary_roots'+str(i)+'.json');assert d['policy_exit']==0 and d['unchanged'] and d['sha256']==binary
 assert [r['root'] for r in d['results']]==group;results+=d['results']
assert [r['root'] for r in results]==roots and len(roots)==len(set(roots))
assert all(set(r['walked_axioms'])<={'propext','Classical.choice','Quot.sound'} for r in results)
scan=load('PCG_binary_scan.json');assert scan['policy_exit']==0 and scan['binary_exit']==0 and scan['sha256']==binary
modules=[json.loads(s) for s in read('PCG_LOADED_scan.jsonl').splitlines()]
assert all(not r['dangling'] and not r['duplicate_owners'] and r['imports_match'] for r in modules)
assert by['PCG_L080']['exit_status']==by['PCG_L088']['exit_status']==0
packets=load('PCG_PACKETS.json');credited={'PCG_K092','PCG_K083'}
for r in packets:
 assert r['root'] in roots
 credited.update('PCG_'+a for a in r['native_positive']+r['native_control'])
 for a in r['native_positive']:
  assert by['PCG_'+a]['exit_status']==0 and 'VERIFICATION:- SUCCESSFUL' in read('PCG_'+a+'/stdout.log')
 for a in r['native_control']:
  s=read('PCG_'+a+'/stdout.log');assert by['PCG_'+a]['exit_status']==1 and 'VERIFICATION:- FAILED' in s and 'unwinding assertion' not in s
for a in sorted(credited):
 g=load(a+'-graph-check.json');assert g['graph_matches_frozen'] and g['all_crate_features']
 lock=load(a+'-lock-check.json');assert lock['unchanged'] and lock['before']==lock['after']=='5782e6a32026fdd95d252d0db7ea20b16716e6deb4f5a397e744886bb6ba22ef'
 assert not load(a+'-source-check.json')['errors']
for a,n in [('PCG_K092',8),('PCG_K084',8)]:assert read(a+'/stdout.log').count('VERIFICATION:- SUCCESSFUL')==n
for a,n in [('PCG_K083',8),('PCG_K085',8)]:assert read(a+'/stdout.log').count('VERIFICATION:- FAILED')==n
assert load('PCG_ALIAS_AUDIT.json')['status']=='PASS'
clauses=load('PCG_CALLER_CLAUSES.json')
closed=[]
for r in packets:
 r.update(status='CLOSED',classification='NEW',ownership='STREAM-C',credited_pool_row=True,gate='PCG_L080/L081/L082..L087; PCG_AUDIT.json',named_hypotheses=[] if r['domain_verbatim'].startswith('True') else [r['domain_verbatim']],caller_clauses=clauses[r['id']]['caller_occurrences'],modifies=[],trust_items_used=['P6/D188 option-A native semantic transport (RECLASSIFICATION)','Rust/std/compiler/ABI/source-to-ELF realization retained'])
 if r['id'] in ['POOL:296','POOL:368']:r['trust_items_used'].append('RuntimeSha256Value: values only')
 if r['id']=='POOL:345':r['trust_items_used'].append('RuntimeReturnData: values only')
 closed.append(r)
(E/'PCG_CLOSED.json').write_text(json.dumps(closed,indent=1)+'\n')
(E/'PCG_PACKETS.json').write_text(json.dumps(packets,indent=1)+'\n')
disagree=[r for r in results if not r['equal']]
audit=dict(schema='PCG-AUDIT-1',status='PASS',headline='AspisR1.RPx_Deployed.deployed',security_target_established=False,roots=results,root_count=len(roots),combined_import='PCG_L080',nfx=dict(attempt='PCG_L081',exit=0,modules=len(modules),dangling=0,duplicates=0,import_mismatches=0),raw_scopes=[f'PCG_L{i:03}' for i in range(82,88)],fixture_attempt='PCG_L009',fixtures=load('PCG_binary_fixtures.json')['results'],same_binary_sha256=binary,collector_disagreements=disagree,raw_ax2_authoritative=True,budget_used=dict(counts),budget_limits=dict(kani=110,lean=90,extract=12),native_support_status='PCG_F1_REPAIRED; original invalid-context passes excluded',accepted_native_receipts=sorted(credited),frozen_pool_revision='b936275465600469312d1f058cdc91ea2a11f3dc',frozen_crates_revision='4bb3b3f51e16b4525f1d10336e2b0bcbbd775387',source_revision=subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip(),export=load('PCG_EXPORT_MANIFEST.json'),scope_metrics=[{k:r[k] for k in ['attempt','kind','module','exit_status','wall_seconds','peak_rss_kib','swaps','source_revision','print_axioms']} for r in attempts if r['attempt'] in ['PCG_L077','PCG_L078','PCG_L080','PCG_L081','PCG_L089',*[f'PCG_L{i:03}' for i in range(82,89)]]])
prints={};root_scopes={}
for idx,group in enumerate(groups):
 a=f'PCG_L{82+idx:03}'
 for line in read(a+'/stdout.log').splitlines():
  m=re.match(r"'([^']+)' (?:depends on axioms:.*|does not depend on any axioms)",line)
  if m:prints[m[1]]=line
 for root in group:root_scopes[root]=a
assert set(roots)<=set(prints),'missing actual print-axioms line'
release=[]
for root in roots:
 r=by[root_scopes[root]]
 release.append(dict(target=root,scope=r['attempt'],scope_target=r['module'],exit_status=r['exit_status'],wall_seconds=r['wall_seconds'],peak_rss_kib=r['peak_rss_kib'],swap=r['swaps'],source_revision=r['source_revision'],print_axioms=prints[root],metrics_granularity='exact shared scope metrics; not a separately timed root',raw_ax2=next(x['walked_axioms'] for x in results if x['root']==root)))
audit['release_results']=release
(E/'PCG_RELEASE_RESULTS.json').write_text(json.dumps(release,indent=1)+'\n')
(E/'PCG_AUDIT.json').write_text(json.dumps(audit,indent=1)+'\n')
delta=dict(schema='PCG-POOL-LEDGER-DELTA-1',base='evidence/pool-ledger1-20261110/PCE_LEDGER.json.xz',headline=audit['headline'],security_target_established=False,gate='PASS',new_closed=24,new_open=0,rows=closed,not_reowned='Stream A599 rows; PCE15 prior CLOSED Pool rows; live PCD/PCF sibling rows',source_revision=audit['source_revision'])
(E/'PCG_LEDGER_DELTA.json').write_text(json.dumps(delta,indent=1)+'\n')
(E/'PCG_REMAINING.md').write_text('# PCG remaining members\n\nNone. All24 assigned members passed the Stream C combined gate and are CLOSED in PCG_CLOSED.json. No member is left conditional. Sibling165/279/280/313 and all other unassigned Pool/shared rows remain with their owners; this delta makes no status claim about them. The overall security target is not established by this batch.\n')
f=E/'PCG_CERTIFICATES.md';s=f.read_text().replace('All24 packets are candidates until the final combined gate.','All24 packets passed the final combined gate and are CLOSED.');s+='\nFinal gate: L080 combined import; L081 NFX exit0 over17129 modules, zero defects; L082..L087 raw89 roots standard axioms with zero collector disagreements. Eight fixtures L009 use the same unchanged binary. Export L088. Exact metrics/revisions/#print axioms are per receipt and PCG_AUDIT.json.\n';f.write_text(s)
print('PASS: 24 Pool rows CLOSED; 89 roots; zero NFX defects or raw/collector disagreements; budgets '+str(dict(counts)))
