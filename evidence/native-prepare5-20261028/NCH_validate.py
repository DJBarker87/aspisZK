from pathlib import Path
import json,hashlib,collections,subprocess,re
E=Path(__file__).resolve().parent
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
rows=[json.loads(l) for l in (E/'NCH_ATTEMPTS.jsonl').read_text().splitlines() if l]
assert len({r['attempt'] for r in rows})==len(rows)
counts=collections.Counter(r['kind'] for r in rows)
assert counts['kani']<=70 and counts['lean']<=60
outcomes=collections.Counter();artifacts={}
for r in rows:
 a=r['attempt'];receipt=E/a/'receipt.json';assert json.loads(receipt.read_text())==r
 assert r['limits']=={'memory.high':'6442450944','memory.max':'8589934592','memory.swap.max':'0','pids.max':'64'}
 assert str(r['swaps'])=='0';assert r['source_revision'];assert r['module'];assert float(r['wall_seconds'])>=0
 admission=json.loads((E/(a+'-reservation.json')).read_text());assert admission['allowed'] is True
 # admission exit0 is additionally evidenced by the wrapper proceeding only under that conjunction.
 log=(E/a/'stdout.log').read_text()
 archived=E/a/'sources'
 for p in archived.rglob('*'):
  if p.is_file():
   n=str(p.relative_to(archived));assert sha(p)==r['source_hashes'][n],(a,n)
 if r['kind']=='kani':
  assert r['env']['CARGO_NET_OFFLINE']=='true' and r['env']['CARGO_PROFILE_DEV_OPT_LEVEL']=='3'
  assert r['copy_patch_sha256']=='bcdf749b78eb6143789500d98d64ec3d407b8a17a6d1290c70c822473e8e9a67'
  assert '--locked' not in r['native_command']
  graph=json.loads((E/(a+'-graph-check.json')).read_text());assert graph['graph_matches_frozen']
  assert json.loads((E/(a+'-lock-check.json')).read_text())['unchanged']
  assert not json.loads((E/(a+'-source-check.json')).read_text())['errors']
  ref=json.loads((E/(a+'-source-pin.json')).read_text());assert sha(E/ref['pinset'])==ref['sha256']
  pins=json.loads((E/ref['pinset']).read_text())['source_sha256']
  for n,h in r['source_hashes'].items():
   rel=n.removeprefix('NCH_src/')
   if rel in pins:assert h==pins[rel],(a,rel)
  assert graph['lock_sha256']=='5782e6a32026fdd95d252d0db7ea20b16716e6deb4f5a397e744886bb6ba22ef'
  if 'timed out' in log.lower():label='TIMEOUT'
  elif 'internal compiler error' in log.lower():label='COMPILER_ICE'
  elif r['exit_status']==0:assert 'VERIFICATION:- SUCCESSFUL' in log;label='PASS'
  elif 'Failed Checks:' in log:label='ASSERTION_FAIL'
  else:label='OTHER_FAIL'
  if a=='NCH_K049' and label=='PASS':label='PASS_QUARANTINED_OPTION_FN'
 else:
  if r['exit_status']==0:
   assert r['print_axioms'] and 'sorryAx' not in log
   for line in r['print_axioms']:
    names=re.search(r'axioms: \[(.*)\]',line)
    if names:assert set(s.strip() for s in names[1].split(',') if s.strip())<={'propext','Classical.choice','Quot.sound'}
   label='PASS'
  else:label='FAILED_DRAFT'
 outcomes[r['kind']+':'+label]+=1
 artifacts[a]={'module':r['module'],'exit':r['exit_status'],'wall_seconds':r['wall_seconds'],'peak_rss_kib':r['peak_rss_kib'],'swaps':r['swaps'],'revision':r['source_revision'],'classification':label,'receipt_sha256':sha(receipt),'stdout_sha256':sha(E/a/'stdout.log')}
assert not (E/'NCH_ACTIVE.json').exists(),'running attempt remains'
large=[str(p) for p in E.rglob('*') if p.is_file() and p.stat().st_size>20*1024*1024];assert not large,large
changed=subprocess.check_output(['git','diff','--name-only','0d728346f9'],text=True).splitlines()
assert all(n.startswith('evidence/native-prepare5-20261028/') or (n.startswith('lean/NCH_') and n.endswith('.lean')) for n in changed),changed
summary={'counts':dict(counts),'outcomes':dict(outcomes),'artifacts':artifacts,'shipped_source_changed':False,'elf_pins_inherited_only':True,'no_release_closure':True}
(E/'NCH_FINAL_ATTEMPTS.json').write_text(json.dumps(summary,indent=2)+'\n')
print(json.dumps({'counts':dict(counts),'outcomes':dict(outcomes),'changed_files':len(changed),'files_over_20MiB':len(large)}))
