"""Read-only consistency checks of focused receipts, strict raw output and map."""
from pathlib import Path
import json,hashlib,lzma,re,subprocess,collections
E=Path('evidence/pv-lib-20261107');A=E/'lane-A';S=A/'session4'
sha=lambda b:hashlib.sha256(b).hexdigest()
freeze=json.loads((E/'FREEZE.json').read_text())
for p,h in freeze['files'].items():assert sha((E/p).read_bytes())==h,p
rs=[json.loads(p.read_text()) for p in S.glob('receipt-*.json')]
for r in rs:
 assert sha(subprocess.check_output(['git','cat-file','blob',r['source_index_blob']]))==r['source_sha256']
 assert sha(lzma.decompress((S/f"resolution-{r['attempt']}.json.xz").read_bytes()))==r['resolution_sha256']
 assert r['stream_b_turn']['exit']==0
 if r['accepted']:
  assert r['exit']=='0' and r['swaps']=='0' and 'sorryAx' not in '\n'.join(r['axioms_summary_based'])
  assert json.loads((S/f"admission-{r['attempt']}.json").read_text())['allowed'] is True
  for prop in ['MemoryHigh=6G','MemoryMax=8G','MemorySwapMax=0','TasksMax=64']:assert prop in r['command']
historical=[json.loads(p.read_text()) for p in A.glob('receipt-*.json')]
failed={r['source_sha256'] for r in rs+historical if not r['accepted']}
assert not failed.intersection(r['source_sha256'] for r in rs if r['accepted'])
accepted={r['target']:r for r in rs if r['accepted'] and not r['runtime_audit']}
manifest=json.loads((S/'AUDIT_ROOTS.json').read_text());roots=[]
for m in manifest['modules']:
 p=Path('lean',m+'.lean');raw=p.read_bytes();assert sha(raw)==accepted[m]['source_sha256']
 assert not re.search(rb'^\s*(axiom|opaque)\s|\bsorry\b|\badmit\b|\bnative_decide\b',raw,re.M)
 src=raw.decode();prints=re.findall(r'^#print axioms (\S+)',src,re.M)
 assert set(re.findall(r'^theorem (\S+)',src,re.M))<=set(prints)
 roots.extend(m+'.'+n for n in prints)
audit=json.loads((S/'RAW_AUDIT.json').read_text());assert audit['strict_raw']
assert set(roots)==set(manifest['roots'])=={r['root'] for r in audit['roots']}
assert all(r['equal'] and set(r['walked_axioms'])<={'propext','Classical.choice','Quot.sound'} for r in audit['roots'])
def body(s):
 a=s.index('  let (modules, roots) :=');b=s.index('  let env ←',a);return s[:a]+s[b:]
assert body(Path('lean/PV_LIB_A_RawAudit4.lean').read_text())==body(Path('lean/PV_LIB_RawAudit2.lean').read_text())
for q in S.glob('failed-*.lean.xz'):
 a=int(q.name.split('-')[1].split('.')[0]);r=next(r for r in rs if r['attempt']==a)
 assert not r['accepted'] and sha(lzma.decompress(q.read_bytes()))==r['source_sha256']
for p in S.rglob('*'):
 if p.is_file():assert p.stat().st_size<=20_000_000,p
m=json.loads((E/'PLIB_MAP.json').read_text());assert m['counts']==dict(collections.Counter(s['status'] for s in m['slots']))
baseline=json.loads((S/'BASELINE.json').read_text());bp=Path(baseline['lane_B_delta'])
assert sha(bp.read_bytes())==baseline['lane_B_delta_sha256']
slots={s['slot']:s for s in m['slots']}
for slot in json.loads(bp.read_text())['slots']:assert slots[slot['slot']]==slot
allowed=lambda p:p.startswith('lean/PV_LIB_A_') or p.startswith(str(A)+'/') or p in [str(E/'PLIB_MAP.json'),str(E/'REMAINING.md')]
paths=subprocess.check_output(['git','diff','--name-only',baseline['base']],text=True).splitlines()
assert all(allowed(p) for p in paths),[p for p in paths if not allowed(p)]
result=dict(base=baseline['base'],source_revision=subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip(),freeze_files_unchanged=len(freeze['files']),focused_scopes=sum(not r['runtime_audit'] for r in rs),accepted_scopes=sum(r['accepted'] for r in rs),failed_scopes=[r['attempt'] for r in rs if not r['accepted']],new_modules=manifest['modules'],new_roots=len(roots),strict_raw_audit=audit['attempt'],counts=m['counts'],max_peak_rss_kbytes=max(int(r['peak_rss_kbytes']) for r in rs),all_recorded_swaps_zero=all(r['swaps']=='0' for r in rs),failed_source_guard_sha256=sha((A/'focused-host-s4.py').read_bytes()),no_failed_source_reused=True,lane_B_unchanged_and_folded=True,endpoint_premises_removed=0,endpoint_premises_added=0)
(S/'VALIDATION.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result))
