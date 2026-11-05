"""Validate committed evidence, budgets, admissions, snapshots and raw/compiled separation."""
from pathlib import Path
import json,hashlib,lzma,re,subprocess
E=Path(__file__).resolve().parent
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
def read(p):
 if p.exists():return p.read_bytes()
 return lzma.decompress(p.with_name(p.name+'.xz').read_bytes())
rows=[json.loads(s) for s in (E/'NHA_ATTEMPTS.jsonl').read_text().splitlines()]
assert len({r['attempt'] for r in rows})==len(rows)
extract=[r for r in rows if r['kind']=='extract'];comp=[r for r in rows if r['kind'] in ['lean','charon']]
assert len(extract)==12 and len(comp)<=25
assert {r['attempt'] for r in extract}=={f'NHA_E{i:03d}' for i in range(1,13)}
for x in rows:
 if x.get('launched') is False:continue
 a=x['attempt'];ad=json.loads((E/(a+'-admission.json')).read_text());assert ad['exit']==0 and ad['reservation']['allowed'] is True,a
 rc=json.loads(read(E/a/'receipt.json'));assert rc['limits']=={'memory.high':'6442450944','memory.max':'8589934592','memory.swap.max':'0','pids.max':'64'},a
 assert int(rc['swaps'])==0 and rc['exit_status'] not in [124,137],a
 for p,h in rc['source_hashes'].items():assert hashlib.sha256(read(E/a/'sources'/p)).hexdigest()==h,(a,p)
 if rc['kind']=='lean':
  assert '-M7000' in rc['command']
  assert any(p.endswith('/Aeneas.olean') for p in rc['deps_fingerprint']['selected_objects']),a
  for line in rc['print_axioms']:
   m=re.search(r'\[([^]]*)\]',line)
   if m:assert set(s.strip() for s in m.group(1).split(','))<={'propext','Classical.choice','Quot.sound'},line
for p in E.glob('NHA_C*-pins.json'):
 x=json.loads(p.read_text());assert x['lock_before']==x['lock_after']=='5782e6a32026fdd95d252d0db7ea20b16716e6deb4f5a397e744886bb6ba22ef'
assert all(x['match'] for x in json.loads((E/'NHA_TOOL_SOURCE_PROVENANCE.json').read_text())['private_hash_checks'].values())
assert all(x['byte_identical_body'] and x['original_body_sha256']==x['scratch_original_body_sha256'] for x in json.loads((E/'NHA_BODY_IDENTITY.json').read_text()))
raw=E/'NHA_emitted/queries_from_pairs';compiled=E/'NHA_lean/NHA_queries_outline'
assert (raw/'Funs.lean').read_bytes()==(compiled/'Funs.lean').read_bytes()
assert (raw/'Types.lean').read_text().replace('@[discriminant isize]\n','')==(compiled/'Types.lean').read_text()
for p in (E/'NHA_lean').rglob('*.lean'):
 assert not re.search(r'\b(sorry|axiom|admit|native_decide)\b',re.sub(r'--[^\n]*','',p.read_text())),p
rc=json.loads(read(E/'NHA_L007/receipt.json'));assert rc['exit_status']==0 and len(rc['print_axioms'])==4
assert not any(p.stat().st_size>20*1024*1024 for p in E.rglob('*') if p.is_file())
assert not list(E.rglob('__pycache__'))
for root in ['crates','programs']:
 assert subprocess.check_output(['git','rev-parse','HEAD:'+root])==subprocess.check_output(['git','rev-parse','4bb3b3f51e16b4525f1d10336e2b0bcbbd775387:'+root])
summary={'valid':True,'extraction_attempts':len(extract),'extraction_successes':[r['attempt'] for r in extract if r['exit_status']==0],'compiler_attempts':len(comp),'lean_invocations':sum(r['kind']=='lean' for r in comp),'charon_invocations':sum(r['kind']=='charon' for r in comp),'prelaunch_exclusions':[r['attempt'] for r in rows if r.get('launched') is False],'wall_sum_seconds':sum(r.get('wall_seconds',0) for r in rows),'peak_rss_kib':max(int(r.get('peak_rss_kib') or 0) for r in rows),'swap':0,'patched_tool_runs':0,'kani_runs':0,'new_theorems':0,'new_closed_rows':0,'shipped_source_identical':True}
(E/'NHA_VALIDATION.json').write_text(json.dumps(summary,indent=2)+'\n');print(json.dumps(summary,indent=2))
