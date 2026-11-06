from pathlib import Path
import json,lzma,hashlib,re,ast,subprocess
E=Path(__file__).resolve().parent;sha=lambda b:hashlib.sha256(b).hexdigest()
ats=[json.loads(l) for l in (E/'NLF_ATTEMPTS.jsonl').read_text().splitlines()]
assert len({x['attempt'] for x in ats})==len(ats)
for r in ats:
 ad=json.loads((E/(r['attempt']+'-admission.json')).read_text());assert ad['exit']==0 and ad['reservation']['allowed'] is True
 assert int(r['swaps'])==0
 assert r['limits']=={'memory.high':'6442450944','memory.max':'8589934592','memory.swap.max':'0','pids.max':'64'}
 assert r['env']['CARGO_TARGET_DIR']=='/home/dombarker/project-offloads/codex-cx-sdk-borrow-20261109/NLF_target'
 assert r['source_revision'] and r['wall_seconds']>=0 and int(r['peak_rss_kib'])>0
inputs=json.loads((E/'NLF_INPUTS.json').read_text())
for h,x in inputs['objects'].items():
 b=(E/x['path']).read_bytes();assert sha(b)==x['archive_sha256'];raw=lzma.decompress(b);assert sha(raw)==h and len(raw)==x['bytes']
for r in ats:
 for n,h in r['source_hashes'].items():assert inputs['attempts'][r['attempt']][n]==h
for p in E.rglob('*.xz'):
 base=p.with_suffix('');side=Path(str(base)+'.sha256')
 if side.exists():assert sha(lzma.decompress(p.read_bytes()))==side.read_text().strip(),str(p)
for p in E.glob('NLF_*.py'):ast.parse(p.read_text(),filename=p.name)
for p in E.glob('NLF_*.lean'):
 assert not re.search(r'\b(sorry|admit|native_decide)\b|^\s*axiom\s|set_option\s+max(?:RecDepth|Heartbeats)',p.read_text(),re.M),p
 assert p.stat().st_size<20*1024*1024
assert not any(p.stat().st_size>20*1024*1024 for p in E.rglob('*') if p.is_file())
fixtures=[];raw=[]
for a,out in [('NLF_L070',fixtures),('NLF_L079',raw)]:
 for line in lzma.decompress((E/a/'stdout.log.xz').read_bytes()).decode().splitlines():
  if line.startswith('NEP_RESULT '):out.append(json.loads(line[11:]))
assert len(fixtures)==8 and all(r['equal'] for r in fixtures)
assert all(bool(x['walked_axioms'])==x['root'].startswith('NEP_Planted.') for x in fixtures)
assert len(raw)==len(json.loads((E/'NLF_AUDIT_ROOTS.json').read_text())['groups'][0])==189
assert all(r['equal'] and set(r['walked_axioms'])<={'propext','Classical.choice','Quot.sound'} for r in raw)
rows=[json.loads(l) for l in lzma.decompress((E/'NLF_NLF_LOADED_scan.jsonl.xz').read_bytes()).decode().splitlines()]
assert all(not r['dangling'] and not r['duplicate_owners'] and r['imports_match'] for r in rows)
for p in E.glob('NLF_K*-graph-check.json'):assert json.loads(p.read_text())['graph_matches_frozen']
for p in E.glob('NLF_K*-lock-check.json'):
 x=json.loads(p.read_text());assert x['unchanged'] and x['before']==x['after']=='5782e6a32026fdd95d252d0db7ea20b16716e6deb4f5a397e744886bb6ba22ef'
assert len(list(E.glob('NLF_K*-graph-check.json')))==60
assert len(list(E.glob('NLF_K*-lock-check.json')))==60
for p in E.glob('NLF_*.lean'):
 if p.stem in ['NLF_ProofDriver','NLF_ScanDriver']:continue
 h=sha(p.read_bytes());assert any(r['module']==p.stem and r['exit_status']==0 and h in r['source_hashes'].values() for r in ats),p
changed=subprocess.check_output(['git','diff','--name-only','61f370f5ced^','--'],text=True).splitlines()
assert all(n.startswith('evidence/sdk-borrow-20261109/') for n in changed)
x=dict(attempts=len(ats),input_objects=len(inputs['objects']),fixture_checks=8,raw_roots=len(raw),scan_modules=len(rows),source_scope_only=True,files_over_20MB=0,all_source_snapshots_pinned=True)
(E/'NLF_VALIDATION.json').write_text(json.dumps(x,indent=1)+'\n');print('NLF local evidence validation passed: '+str(len(ats))+' scope receipts')
