"""Local receipt/source/size/budget hygiene; no compiler/prover replay."""
from pathlib import Path
import json,lzma,hashlib,subprocess,time,resource,sys,collections
E=Path(__file__).resolve().parent;start=time.monotonic();sha=lambda b:hashlib.sha256(b).hexdigest();read=lambda p:json.loads(p.read_text());rs=[json.loads(l) for l in (E/'NIJ_ATTEMPTS.jsonl').read_text().splitlines()];idx=read(E/'NIJ_INPUTS.json');assert len({r['attempt'] for r in rs})==len(rs)
for h,o in idx['objects'].items():
 b=(E/o['path']).read_bytes();assert sha(b)==o['archive_sha256'] and sha(lzma.decompress(b))==h
checked=0
for r in rs:
 if not r.get('source_hashes'):continue
 hashes=idx['attempts'][r['attempt']]
 for n,h in r['source_hashes'].items():assert hashes[n]==h;(checked:=checked+1)
 assert r['limits']=={'memory.high':'6442450944','memory.max':'8589934592','memory.swap.max':'0','pids.max':'64'}
 assert str(r['swaps'])=='0' and r['source_revision']
 if r['kind']=='lean' and r['exit_status']==0:assert all('sorryAx' not in x for x in r['print_axioms'])
for kind,limit in [('K',120),('L',51),('E',2)]:
 ids={r['attempt'] for r in rs if len(r['attempt'])==8 and r['attempt'].startswith('NIJ_'+kind)}
 if kind=='L':ids.add('NIJ_L038')
 assert ids=={'NIJ_'+kind+f'{i:03}' for i in range(1,limit+1)},(kind,ids)
for p in E.rglob('*'):
 if not p.is_file():continue
 assert p.stat().st_size<=20*1024*1024,p
 assert p.suffix not in ['.olean','.elf','.so'],p
assert not list(E.rglob('__pycache__'))
c=read(E/'NIJ_CLOSED.json');assert c['new_composed_rows']==c['new_composed_functions']==0 and c['functions']==[]
a=read(E/'NIJ_AUDIT.json');assert a['formal_status']=='PASS_AX2_NFX' and a['admission_status']=='DENIED_NATIVE_OUTPUT_ISOLATION'
assert read(E/'NIJ_HOST_FINAL.json')['keys_deleted'] is False
b=dict(authorized=dict(kani=120,lean=90,extraction=2),consumed_slots=dict(kani=120,lean=51,extraction=2),formal_no_launch_slots=['NIJ_L038'],extra_initial_no_launch_preflight='NIJ_K001-preflight: no additional allocated K slot',unused=dict(kani=0,lean=39,extraction=0),total_consumed=173,total_authorized=212,fraction=173/212,remaining_review='NIJ_REMAINING.md: remaining requirements are native associations, suspended-credit or isolation review, not independent Lean equations',scope_receipt_counts=dict(collections.Counter(r.get('kind','preflight') for r in rs)))
(E/'NIJ_BUDGET.json').write_text(json.dumps(b,indent=1)+'\n')
out=dict(target='receipt/source/budget/size/final-admission hygiene',exit_status=0,wall_seconds=time.monotonic()-start,peak_rss_kib=resource.getrusage(resource.RUSAGE_SELF).ru_maxrss//(1024 if sys.platform=='darwin' else 1),swaps=resource.getrusage(resource.RUSAGE_SELF).ru_nswap,source_revision=subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip(),source_sha256=sha(Path(__file__).read_bytes()),print_axioms='N/A Python; standard-only formal roots in NIJ_AUDIT.json',source_snapshots_checked=checked,input_objects=len(idx['objects']),new_closed_rows=0,withheld_candidates=3,shipped_changes=False)
(E/'NIJ_FINAL_VALIDATION.json').write_text(json.dumps(out,indent=1)+'\n');print(json.dumps(out))
