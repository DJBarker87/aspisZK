"""Additive receipt and open-obligation validator; never promotes local facts."""
from pathlib import Path
import json,hashlib,sys,re,lzma,subprocess
E=Path(__file__).resolve().parent;P=E.parent/'transcript-queries-20261105'
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
corr=json.loads((E/'NHB_SOURCE_CORRESPONDENCE.json').read_text())
assert all(x['equal'] and x['frozen']['sha256']==x['historical']['sha256'] for x in corr['functions'])
assert sha(P/'NGQ_FROZEN_INPUTS.json.xz')==corr['frozen_inputs_sha256']
frozen=json.loads(lzma.decompress((P/'NGQ_FROZEN_INPUTS.json.xz').read_bytes()))['crates/aspis-core/src/r0_transcript.rs']
historical=subprocess.check_output(['git','show',corr['comparison_revision']+':'+corr['historical_path']],text=True)
for row in corr['functions']:
 for label,source in [('frozen',frozen),('historical',historical)]:
  expected=row[label];a=source.index(row['needle']);i=source.index('{',a)+1;depth=1
  while depth:depth+=(source[i]=='{')-(source[i]=='}');i+=1
  assert source[a:i]==expected['text'] and hashlib.sha256(source[a:i].encode()).hexdigest()==expected['sha256']
  assert source[:a].count('\n')+1==expected['start_line'] and source[:i].count('\n')+1==expected['end_line']

assert all(sha(Path(p))==h for p,h in json.loads((E/'NHB_REUSE.json').read_text()).items())
results=[]
for p in sorted(E.glob('NHB_K[0-9][0-9][0-9]/receipt.json')):
 r=json.loads(p.read_text());a=r['attempt'];raw=(p.parent/'stdout.log').read_text()
 graph=json.loads((E/(a+'-graph-check.json')).read_text());lock=json.loads((E/(a+'-lock-check.json')).read_text())
 assert graph['graph_matches_frozen'] and lock['unchanged'],a
 assert r['swaps']=='0',a
 assert r['limits']=={'memory.high':'6442450944','memory.max':'8589934592','memory.swap.max':'0','pids.max':'64'},a
 ad=json.loads((E/(a+'-admission.json')).read_text());assert ad['exit']==0 and ad['reservation']['allowed'] is True,a
 if 'timed out' in raw or 'CBMC failed' in raw:verdict='TOOL_LIMIT'
 elif r['exit_status']==0 and 'VERIFICATION:- SUCCESSFUL' in raw:verdict='PASS'
 elif 'Failed Checks:' in raw and re.search(r'\*\* 1 of \d+ failed',raw) and 'unwinding assertion' not in raw:verdict='ASSERTION_FAILED'
 else:verdict='OTHER_FAILURE'
 results.append(dict(attempt=a,target=r['module'],verdict=verdict,receipt_sha256=sha(p)))
 if int(a[-3:])>=3:
  src=p.parent/'sources/NHB_src/crates/aspis-core/src/NHB_harness.rs'
  assert '#[kani::stub(core::ptr::copy_nonoverlapping,crate::KMX_stubs::KMX_copy_nonoverlapping)]' in src.read_text(),a
pairs=[(3,4),(5,6),(7,8),(9,10),(11,12),(13,14),(15,16),(20,21),(22,23),(24,25),(26,27),(30,31),(43,44),(46,47),(50,51),(53,54),(55,56)]
for pos,neg in pairs:
 a=f'NHB_K{pos:03d}';b=f'NHB_K{neg:03d}';rd={x['attempt']:x for x in results}
 assert rd[a]['verdict']=='PASS' and rd[b]['verdict']=='ASSERTION_FAILED',(a,b)
 cfg=[json.loads((E/(n+'.json')).read_text()) for n in [a,b]]
 assert cfg[0]['native_command']==cfg[1]['native_command'],(a,b)
 for n in [a,b]:
  rr=json.loads((E/n/'receipt.json').read_text())
  assert rr['exit_status'] not in [124,137],n
for p in E.glob('NHB_L[0-9][0-9][0-9]/receipt.json'):
 r=json.loads(p.read_text())
 if r['exit_status']==0:
  for line in r['print_axioms']:
   assert 'sorryAx' not in line and 'axioms: [' not in line or all(x.strip() in ['propext','Classical.choice','Quot.sound'] for x in line.split('axioms: [',1)[1].rstrip(']').split(',')),line
if (E/'NHB_LEDGER_DELTA.json').exists():
 d=json.loads((E/'NHB_LEDGER_DELTA.json').read_text())
 assert d.get('newly_closed',[])==[], 'Physical producer not yet validated; no promotion authorized by this validator'
(E/'NHB_NATIVE_RESULTS.json').write_text(json.dumps(dict(runs=results,composed_row_credit=False),indent=2)+'\n')
print(json.dumps(dict(native_receipts=len(results),correspondence_functions=len(corr['functions']),status='PASS',physical_producer='OPEN')))
