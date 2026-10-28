"""Audit terminal native verdicts, exact control locations and frozen inputs."""
from pathlib import Path
import json,re,hashlib
E=Path(__file__).resolve().parent
rows=[]
for i,shape in enumerate(json.loads((E/'NCM_NATIVE_SHAPES.json').read_text())):
 pair=[]
 for j,side in enumerate(['positive','negative']):
  a=f'NCM_K{2*i+j+1:03}';p=E/a/'receipt.json'
  if not p.exists():continue
  r=json.loads(p.read_text());s=(p.parent/'stdout.log').read_text();g=json.loads((E/(a+'-graph.json')).read_text())
  assert g['allowed'] and not g['new_packages'] and not g['edge_errors']
  assert g['unchanged'] and g['lock_before']==g['lock_after']=='5782e6a32026fdd95d252d0db7ea20b16716e6deb4f5a397e744886bb6ba22ef'
  assert g['KMX_patch_sha256']=='bcdf749b78eb6143789500d98d64ec3d407b8a17a6d1290c70c822473e8e9a67'
  assert r['limits']=={'memory.high':'6442450944','memory.max':'8589934592','memory.swap.max':'0','pids.max':'64'}
  assert r['env']['CARGO_NET_OFFLINE']=='true' and r['env']['CARGO_PROFILE_DEV_OPT_LEVEL']=='3'
  verdict='PASS' if 'VERIFICATION:- SUCCESSFUL' in s else 'FAIL' if 'VERIFICATION:- FAILED' in s else 'NO_VERDICT'
  fail=s[s.rfind('Failed Checks:'):s.rfind('VERIFICATION:-')].strip() if verdict=='FAIL' else ''
  intended=None
  if side=='negative':
   if shape['shape']=='key_read':intended='NCM_candidate.rs", line 14'
   else:intended='NCM_spy.rs", line '+str({'geometry':8,'first':9,'second':10,'reply':15}[shape['shape'].rsplit('_',1)[1]])
  ok=(side=='positive' and verdict=='PASS' and r['exit_status']==0) or (side=='negative' and verdict=='FAIL' and r['exit_status']==1 and intended in fail and re.search(r'\*\* 1 of \d+ failed',s) is not None)
  pair.append(dict(attempt=a,side=side,verdict=verdict,expected_verdict_confirmed=ok,failing_check=fail,exit=r['exit_status'],wall_seconds=r['wall_seconds'],peak_rss_kib=r['peak_rss_kib'],swaps=r['swaps'],source_revision=r['source_revision'],source_hashes=r['source_hashes']))
 rows.append(dict(**shape,runs=pair,matched_credit=len(pair)==2 and all(x['expected_verdict_confirmed'] for x in pair),K2='not quarantined: data-only observer, no Option<fn> or function-pointer-valued state',credit_scope='actual helper only; NOT full NCE fragment'))
out=dict(rows=rows,total_runs=sum(len(x['runs']) for x in rows),matched_shapes=sum(x['matched_credit'] for x in rows),full_NCE_fragments_closed=0)
(E/'NCM_NATIVE_AUDIT.json').write_text(json.dumps(out,indent=2)+'\n')
(E/'NCM_NATIVE_VERDICTS.jsonl').write_text(''.join(json.dumps(dict(attempt=r['attempt'],shape=row['shape'],side=r['side'],harness=row['module']+'::'+row[r['side']],verdict=r['verdict'],exit=r['exit'],expected_verdict_confirmed=r['expected_verdict_confirmed']))+'\n' for row in rows for r in row['runs']))
print({k:v for k,v in out.items() if k!='rows'})
