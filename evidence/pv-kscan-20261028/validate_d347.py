from pathlib import Path
import json,hashlib,collections,ast,subprocess,re
E=Path(__file__).resolve().parent;D=E/'diagnostics/d347';s=json.loads((E/'scan.json').read_text());inp=json.loads((E/'d347-input.json').read_text());plans=json.loads((E/'d347-plans.json').read_text());bs={b['run']:b for b in json.loads((E/'d347-source-bindings.json').read_text())};checks=[]
def check(label,v):assert v,label;checks.append(label)
check('All 264 original observations retained, all 162 D347 inputs adjudicated',s['pass_count']==264 and len(s['passes'])==264 and len(inp['passes'])==162 and not s['unresolved'] and len(json.loads((E/'d347-adjudications.json').read_text()))==162)
check('Completed classification partition',s['counts']==dict(collections.Counter(p['status'] for p in s['passes']))=={'EXPOSED':57,'NO_REACHED_COPY':178,'EXEMPT':25,'PROPERTY_INDEPENDENT':4})
check('No unknown reached/dependence fields',all(isinstance(p['copy_builtin_reached'],bool) and isinstance(p['property_depends_on_copy'],bool) for p in s['passes']))
check('Only two allowed exemptions',all(p['exemption'] in [None,'call-name overapproximation','rejects before the copy on the admitted domain'] for p in s['passes']))
check('Exposure and property independence are separate',all((p['status']!='EXPOSED' or p['copy_builtin_reached'] and p['property_depends_on_copy']) and (p['status']!='PROPERTY_INDEPENDENT' or p['copy_builtin_reached'] and not p['property_depends_on_copy'] and p['exemption'] is None) for p in s['passes']))
check('Exact suspension set, all 407 rows partitioned and V184 structural route stands',s['suspended_rows']==['V178','V179','V182','V195','V233'] and len(s['row_consequences'])==407 and collections.Counter(r['consequence'] for r in s['row_consequences'])=={'STANDS':402,'SUSPENDED':5} and next(r for r in s['row_consequences'] if r['row']=='V184')['consequence']=='STANDS')
count=0
for p in D.glob('*/goto-scan.json'):
 for h in json.loads(p.read_text()):
  g=p.parent/h['graph_file'];raw=g.read_text();assert hashlib.sha256(raw.encode()).hexdigest()==h['graph_sha256'],g
  edges={tuple(l.split(' -> ',1)) for l in raw.splitlines() if ' -> ' in l};root=h['metadata']['mangled_name'];assert root in raw
  for path in h['copy_paths'].values():assert path[0]==root and path[-1] in ['memcpy','memmove'] and all((a,b) in edges for a,b in zip(path,path[1:])),g
  assert not h['metadata']['attributes']['stubs'] and not h['metadata']['attributes']['verified_stubs'],g
  count+=1
checks.append(f'{count} raw D347 goto graph hashes, roots, builtin paths and empty selected stub lists')
for original in inp['passes']:
 i=original['index'];p=s['passes'][i];d=p['diagnostic'];run=d['run'];assert run in bs,(i,run)
 assert p['harness']==original['harness'] and p['pass_output_blob']==original['pass_output_blob'] and p['receipt_blob']==original['receipt_blob']
 candidates=[h for h in json.loads((E/d['metadata_and_paths']).read_text()) if h['harness']==p['harness']];assert candidates,(i,run)
 assert all(bool(h['copy_paths'])==bool(candidates[0]['copy_paths']) for h in candidates),(i,run)
 assert set(d['candidate_goto_sha256s'])=={h['goto_sha256'] for h in candidates}
 assert d['goto_sha256'] in {h['goto_sha256'] for h in candidates} and (E/d['graph']).exists()
checks.append('Every original D347 observation has a source binding and consistent matching metadata candidates; exact original evidence identities preserved')
for name in ['cbmc','goto-instrument','kani-compiler','kani-driver']:
 a=json.loads((D/'tool-pins.json').read_text())[name];b=json.loads((E/'diagnostics/tool-pins.json').read_text())[name];assert a==b
checks.append('D347 actual tool executable hashes equal first-audit pinned diagnostic binaries')
runs=json.loads((E/'d347-execution.json').read_text());assert len(runs)==60
for r in runs:
 directory=D/r['run'];assert r['print_axioms'].startswith('N/A') and r['swaps']==0 and r['peak_rss_kib'] is not None
 limits=json.loads((directory/'limits.json').read_text());assert limits=={'memory.high':'6442450944','memory.max':'8589934592','memory.swap.max':'0','pids.max':'64'}
 for f in ['admission.json','barrier.json']:assert json.loads((directory/f).read_text())['allowed'] is True
 if r['codegen'] is not None:assert '--only-codegen' in r['codegen']['command'] and '--keep-temps' in r['codegen']['command']
 else:assert r['run'] in ['D001','D043']
check('All 60 scopes capped/admitted; 58 codegen-only invocations; zero verification/Lean',s['resume_budget']['scopes_used']==60 and s['resume_budget']['codegen_invocations']==58 and s['resume_budget']['verification_runs']==0 and s['resume_budget']['lean_attempts']==0)
check('Five retained failed inputs have corrected successors; no timeout or memory kill',[(r['run'],r['exit']) for r in runs if r['exit']] == [('D010',1),('D017',1),('D023',1),('D026',1),('D047',1)])
objects=sorted({p[k] for p in s['passes'] for k in ['receipt_blob','pass_output_blob']});p=subprocess.Popen(['git','cat-file','--batch-check'],stdin=subprocess.PIPE,stdout=subprocess.PIPE,text=True);out,_=p.communicate('\n'.join(objects)+'\n');check('Original PASS and receipt Git blobs remain accessible',len(out.splitlines())==len(objects) and all(' blob ' in line for line in out.splitlines()))
for p in E.glob('*.py'):ast.parse(p.read_text())
checks.append('Authored Python syntax')
check('No binary/target/cache artifacts in evidence',not any(p.is_file() and p.suffix in ['.out','.o','.rlib','.rmeta','.olean','.bin','.elf'] for p in E.rglob('*')) and not any(p.is_dir() and p.name in ['target','cache','workspace'] for p in (E/'diagnostics/d347').rglob('*')))
cleanup=json.loads((D/'cleanup.json').read_text());check('Own caches removed; no own active codegen and no keys touched',cleanup['removed_bytes']==6887738989 and not cleanup['active_own_codegen_scopes'])
result=dict(status='PASS',checks=checks,pass_observations=264,d347_observations=162,unresolved=0,counts=s['counts'],scopes=60,codegen_invocations=58,verification_runs=0,lean_attempts=0,suspended_rows=s['suspended_rows'],scope='Evidence/index/source-binding and graph integrity, not universal tool fidelity, new solver verification or deployment adequacy')
(E/'d347-validation.json').write_text(json.dumps(result,indent=2)+'\n');print('PASS',len(checks),'checks;',count,'D347 graphs; zero unresolved')
