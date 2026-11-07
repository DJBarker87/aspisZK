"""Evidence/source consistency only; never starts a proof replay."""
from pathlib import Path
import json,hashlib,lzma,re,subprocess,collections
E=Path('evidence/pv-lib-20261107');A=E/'lane-A';sha=lambda b:hashlib.sha256(b).hexdigest()
freeze=json.load(open(E/'FREEZE.json'))
for p,h in freeze['files'].items():assert sha((E/p).read_bytes())==h,p
receipts=[json.load(open(q)) for q in sorted(A.glob('receipt-*.json'))];accepted={r['target']:r for r in receipts if r['accepted'] and not r['runtime_audit']}
for r in receipts:
 blob=subprocess.check_output(['git','cat-file','blob',r['source_index_blob']]);assert sha(blob)==r['source_sha256'],r['attempt']
 assert sha(lzma.decompress((A/f"resolution-{r['attempt']}.json.xz").read_bytes()))==r['resolution_sha256']
 assert r['stream_b_turn']['exit']==0 and r['stream_b_turn']['command'][-1]=='STREAMB_SLOTS=3 /home/dombarker/streamb-slots/turn.sh'
 if r['accepted']:
  assert r['exit']=='0' and r['swaps']=='0' and 'sorryAx' not in '\n'.join(r['axioms_summary_based'])
  assert json.load(open(A/f"admission-{r['attempt']}.json"))['allowed'] is True
  for prop in ['MemoryHigh=6G','MemoryMax=8G','MemorySwapMax=0','TasksMax=64']:assert prop in r['command']
provider_inputs={}
for name in ['PURE_REPLAY_PLAN','DROP_REPLAY_PLAN','SOURCE_REPLAY_PLAN','NUMBER_REPLAY_PLAN','NAME_REPLAY_PLAN']:
 for x in json.load(open(A/(name+'.json'))):
  raw=subprocess.check_output(['git','show',x['revision']+':lean/'+x['module']+'.lean'])
  assert sha(raw)==x['source_sha256'] and Path(x['source_path']).read_bytes()==raw
  provider_inputs[x['module']]=dict(revision=x['revision'],source_sha256=sha(raw),compiled_in_this_lane=x['module'] in accepted)
modules=json.load(open(A/'AUDIT_ROOTS.json'))['modules'];roots=[]
for m in modules:
 raw=Path('lean',m+'.lean').read_bytes();assert accepted[m]['source_sha256']==sha(raw),m
 assert not re.search(rb'^\s*(axiom|opaque)\s|\bsorry\b|\badmit\b|\bnative_decide\b',raw,re.M),m
 src=raw.decode();theorems=re.findall(r'^theorem (\S+)',src,re.M);printed=re.findall(r'^#print axioms (\S+)',src,re.M)
 assert set(theorems)<=set(printed),(m,theorems,printed)
 roots.extend(m+'.'+r for r in printed)
raw=json.load(open(A/'RAW_AUDIT.json'));assert raw['strict_raw'] and raw['root_count']==len(roots)==43
assert {r['root'] for r in raw['roots']}==set(roots)
assert all(r['equal'] and set(r['walked_axioms'])<={'propext','Classical.choice','Quot.sound'} for r in raw['roots'])
# Strict driver body is byte-identical apart from its two input arrays.
def driver_body(s):
 a=s.index('  let (modules, roots) :=');b=s.index('  let env ←',a);return s[:a]+s[b:]
base=subprocess.check_output(['git','show','5e397cb3878:lean/PV_LIB_RawAudit2.lean'],text=True)
assert driver_body(base)==driver_body(Path('lean/PV_LIB_A_RawAudit.lean').read_text())
for q in A.glob('failed-*.lean.xz'):
 attempt=int(q.name.split('-')[1].split('.')[0]);r=next(r for r in receipts if r['attempt']==attempt)
 assert not r['accepted'] and sha(lzma.decompress(q.read_bytes()))==r['source_sha256']
for p in A.rglob('*'):
 if p.is_file():assert p.stat().st_size<=20_000_000,p
m=json.load(open(E/'PLIB_MAP.json'));delta=json.load(open(A/'MAP_DELTA.json'))
assert m['counts']==dict(collections.Counter(s['status'] for s in m['slots']))==delta['counts_after']
base=json.loads(subprocess.check_output(['git','show','5e397cb3878:evidence/pv-lib-20261107/PLIB_MAP.json']))
bslots={s['slot']:s for s in base['slots']};changed={s['slot'] for s in m['slots'] if s!=bslots[s['slot']]}
assert changed=={s['slot'] for s in delta['changed_slots']}
allowed=lambda p:p.startswith('lean/PV_LIB_A_') or p.startswith(str(A)+'/') or p in [str(E/'PLIB_MAP.json'),str(E/'REMAINING.md')]
paths=subprocess.check_output(['git','diff','--name-only','5e397cb3878'],text=True).splitlines()
assert all(allowed(p) for p in paths),[p for p in paths if not allowed(p)]
result=dict(base='5e397cb3878',source_revision=subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip(),freeze_files_unchanged=len(freeze['files']),focused_scopes=sum(not r['runtime_audit'] for r in receipts),passing_focused_scopes=sum(r['accepted'] and not r['runtime_audit'] for r in receipts),failed_focused_scopes=[r['attempt'] for r in receipts if not r['accepted']],new_library_modules=modules,new_library_root_count=len(roots),strict_raw_audit=49482,source_authority_checks=provider_inputs,counts=m['counts'],scope_boundary='Own modules/evidence plus shared map JSON and REMAINING only; no endpoint/ledger/package changes',max_peak_rss_kbytes=max(int(r['peak_rss_kbytes']) for r in receipts),all_recorded_swaps_zero=all(r['swaps']=='0' for r in receipts))
(A/'VALIDATION.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps({k:result[k] for k in ['focused_scopes','passing_focused_scopes','failed_focused_scopes','new_library_root_count','counts','max_peak_rss_kbytes']}))
