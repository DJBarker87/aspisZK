"""Final bounded evidence checks. No theorem/native proof is replayed."""
from pathlib import Path
import json,lzma,hashlib,sys,shutil
B=Path.cwd();mode=sys.argv[1];H=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
def write(n,x):(B/n).write_text(json.dumps(x,indent=2)+'\n')
if mode=='native':
 sources=json.loads((B/'NLZ_SOURCE_PINS.json').read_text());assert all(H(B/'NLZ_src'/n)==h for n,h in sources.items())
 assert H(B/'NLZ_src/Cargo.lock')=='5782e6a32026fdd95d252d0db7ea20b16716e6deb4f5a397e744886bb6ba22ef'
 assert H(B/'NLZ_KMX.patch')=='bcdf749b78eb6143789500d98d64ec3d407b8a17a6d1290c70c822473e8e9a67'
 rows=[]
 for j in range(1,41):
  a=f'NLZ_K{j:03}';rc=json.loads((B/a/'receipt.json').read_text());graph=json.loads((B/(a+'-graph-check.json')).read_text());lock=json.loads((B/(a+'-lock-check.json')).read_text());assert graph['graph_matches_frozen']and lock['unchanged']
  log=(B/a/'stdout.log').read_text();control=rc['module'].endswith('_control')
  verdict='PASS'if rc['exit_status']==0 and'VERIFICATION:- SUCCESSFUL'in log else'CONTROL_FAIL'if control and('Failed Checks: assertion failed: !good'in log or 'Failed Checks: assertion failed: good && log.phase'in log) and'CBMC timed out'not in log else'TIMEOUT'if'CBMC timed out'in log else'INPUT_FAILURE'
  rows.append(dict(attempt=a,verdict=verdict,module=rc['module'],exit=rc['exit_status'],source_pins_sha256=H(B/a/'sources/NLZ_SOURCE_PINS.json')))
 pairs=[(4,2),(5,6),(17,18),(19,20),(21,22),(23,24)]+[(j,j+1)for j in [9,11,13,15]+list(range(27,41,2))]
 checked=[]
 for p,c in pairs:
  a,b=rows[p-1],rows[c-1]
  matched=a['verdict']=='PASS'and b['verdict']=='CONTROL_FAIL'and a['source_pins_sha256']==b['source_pins_sha256']
  checked.append(dict(positive=p,control=c,matched_configuration=matched,control_kind='corrupted_logged_reply'if p>=27 else'inverted_assertion_only',full_native_credit=False))
 out=dict(status='RETAINED_NATIVE_CANDIDATE_EVIDENCE',runs=rows,pairs=checked,matched_configurations=sum(x['matched_configuration']for x in checked),corrupted_reply_pairs=sum(x['matched_configuration']and x['control_kind']=='corrupted_logged_reply'for x in checked),native_parent_realization=False,closed_rows=[],quarantined_option_fn=[],suspended_writable_static=[])
 write('NLZ_NATIVE_FINAL.json',out)
elif mode=='retention':
 count=0
 for p in(B/'NLZ_audit').rglob('*.xz'):
  raw=lzma.decompress(p.read_bytes());q=Path(str(p)[:-3]+'.sha256');assert q.is_file()and hashlib.sha256(raw).hexdigest()==q.read_text().strip(),str(p);count+=1
 for name in ['NLZ_CLOSURE_PINS.json.xz','NLZ_NLR_CLOSURE_PINS.json.xz','NLZ_NLS_CLOSURE_PINS.json.xz']:
  x=json.loads(lzma.decompress((B/name).read_bytes()))
  for r in x['selected_objects']:assert H(Path(r['path']))==r['sha256'],r['path']
 own=sum(p.stat().st_size for p in B.rglob('*')if p.is_file());assert own<30_000_000_000
 out=dict(status='PASS',compressed_sha_pairs=count,own_host_bytes=own,disk=shutil.disk_usage(B)._asdict(),deletions=0,cache_retained=True)
 write('NLZ_RETENTION.json',out)
elif mode=='audit':
 plan=json.loads((B/'NLZ_AUDIT_PLAN.json').read_text());expected=json.loads((B/'NLZ_AUDIT_ROOTS.json').read_text())['roots'];roots=[];mismatches=[];groups=[]
 for j in range(plan['groups']):
  r=json.loads((B/'NLZ_audit'/('proof'+str(j))/('proof'+str(j)+'.json')).read_text());groups.append({k:v for k,v in r.items()if k not in ['results','print_axioms']})
  for v in r['results']:
   assert set(v['walked_axioms'])<={'propext','Classical.choice','Quot.sound'},v
   roots.append(v['root'])
   if not v['equal']:mismatches.append(v)
 assert sorted(roots)==sorted(expected),'Missing/repeated raw roots'
 scan=[json.loads(l)for l in(B/'NLZ_LOADED_scan.jsonl').read_text().splitlines()];assert all(not r['dangling']and not r['duplicate_owners']and r['imports_match']for r in scan)
 fixture=json.loads((B/'NLZ_audit/fixtures/fixtures.json').read_text());assert len(fixture['results'])==8 and all(r['equal']for r in fixture['results'])
 comparison=json.loads((B/'NLZ_PREDECESSOR_COMPARISON.json').read_text());assert all(r['status']=='PASS'for r in comparison.values())
 out=dict(status='PASS_STANDARD_RAW_WITH_RETAINED_COLLECTOR_DISAGREEMENTS'if mismatches else'PASS',target_established=False,headline='AspisR1.RPx_Deployed.deployed',combined_audits=1,scan_modules=len(scan),dangling=0,duplicate_owners=0,import_mismatches=0,raw_roots=len(roots),raw_groups=groups,raw_all_standard=True,collector_disagreements=mismatches,fixtures=fixture,predecessor_comparison=comparison,closed_rows=[],qualified_rows=[],full_resource_packets=False)
 write('NLZ_AUDIT.json',out)
elif mode=='final':
 assert json.loads((B/'NLZ_AUDIT.json').read_text())['raw_all_standard']
 for r in json.loads((B/'NLZ_PROOF_SOURCE.json').read_text())['sources']:assert H(Path(r['path']))==r['sha256']
 for r in json.loads((B/'NLZ_EXPORT.json').read_text())['files']:assert H(Path(r['path']))==r['sha256']
 out=dict(status='PASS_FINAL_RETENTION',target_established=False,source_manifest_sha256=H(B/'NLZ_PROOF_SOURCE.json'),closure_manifest_sha256=H(B/'NLZ_CLOSURE_PINS.json.xz'),cache_retained=True,closed_rows=[],qualified_rows=[],full_rowspec136=False,full_rowspec137=False,full_rowspec087=False)
 write('NLZ_FINAL.json',out)
else:raise AssertionError(mode)
print(json.dumps({k:v for k,v in out.items()if k not in ['runs','pairs','raw_groups','collector_disagreements','fixtures','predecessor_comparison']}))
