"""adopted by owner decision D502/D478. Report exact focused receipts, without promoting native or lead-only work."""
from pathlib import Path
import json,re,hashlib,subprocess
E=Path('evidence/pv-evh-20261029')
rs=sorted((json.load(open(q)) for q in E.glob('receipt-*.json')),key=lambda r:r['attempt'])
allowed={'propext','Classical.choice','Quot.sound'}
for r in rs:
 if r['accepted']:
  assert r['exit']=='0'
  for line in r['axioms']:
   if 'depends on axioms:' in line:
    names=set(re.search(r'\[([\s\S]*?)\]',line)[1].replace('\n','').replace(' ','').split(','))
    assert names<=allowed,(r['attempt'],names)
  assert r['swaps']=='0'
  assert r['admission']['allowed'] is True
summary=dict(lean_attempts=len(rs),accepted=sum(r['accepted'] for r in rs),
 rejected=sum(not r['accepted'] for r in rs),native_scopes=0,kani=0,
 admission_refusals=len(list(E.glob('refusal-history-*.json')))+1,
 max_peak_rss_kbytes=max(int(r['peak_rss_kbytes']) for r in rs),
 swaps=sum(int(r['swaps']) for r in rs),void_launches=0,
 guard_sha256=hashlib.sha256(Path('tools/pv-evh-20261029/compile.py').read_bytes()).hexdigest(),
 current_revision=subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip(),
 forbidden_worker_target='PV_EVH_FixtureConsumer',attempts=rs)
(E/'summary.json').write_text(json.dumps(summary,indent=2)+'\n')
lines=['# AGENTS.md section 6 focused receipts','',
 '| ID | Exact target | Exit | Wall | Peak RSS KiB | Swap | Source revision |',
 '|---|---|---:|---|---:|---:|---|']
for r in rs:
 lines.append(f"| {r['attempt']} | `{r['target']}` | {r['exit']} | {r['wall']} | {r['peak_rss_kbytes']} | {r['swaps']} | `{r['source_revision']}` |")
lines+=['','Every row links by ID to `receipt-ID.json`, `out-ID.log`, `time-ID.log`.',
 'The JSON receipts contain complete original #print axioms lines, source SHA256,',
 'dependency fingerprint, admission result and exact capped command.',
 'Rejected elaborations and their sorryAx diagnostic outputs are uncredited;',
 'only accepted results with standard axioms are consumed.','',
 'Failed-source guard SHA256: `'+summary['guard_sha256']+'`.','',
 f"Actual Lean launches: {len(rs)}. Native scopes: 0. Kani: 0. VOID launches: 0.",
 'Refused pre-compiler admission checks are retained separately and uncharged.']
(E/'receipts.md').write_text('\n'.join(lines)+'\n')
print(json.dumps({k:v for k,v in summary.items() if k!='attempts'},indent=2))
