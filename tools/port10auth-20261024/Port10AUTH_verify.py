from pathlib import Path
import hashlib,json,re,subprocess
R=Path(__file__).resolve().parents[2]; T=R/'tools/port10auth-20261024'; E=R/'evidence/port10auth-20261024'; L=R/'docs/research/100bit-spend-path-20261013/lean'
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
configs=sorted(T.glob('lean-*.json'));receipts=sorted(E.glob('lean-*/receipt.json'))
assert len(configs)==len(receipts)==64
assert [p.stem for p in configs]==[f'lean-{n:03d}' for n in range(1,65)]
rs=[json.loads(p.read_text()) for p in receipts];manifest=json.loads((E/'manifest.json').read_text())
assert (manifest['inherited_lean_attempts'],manifest['cumulative_lean_attempts'],manifest['remaining_lean_attempts'])==(96,160,0)
for r in rs:
 for name,h in r['source_hashes'].items(): assert sha(E/r['attempt']/'sources'/name)==h
 reservation=json.loads((E/(r['attempt']+'-reservation.json')).read_text())
 assert reservation['reserved_bytes']+reservation['additional_bytes']<=55*1024**3
 if r['attempt']=='lean-033':
  assert r['status'].startswith('Pre-Lean') and r['wall_seconds'] is None
  continue
 assert r['limits']=={'memory.high':'6442450944','memory.max':'8589934592','memory.swap.max':'0','pids.max':'64'}
 assert r['swaps']=='0'
 assert r['deps_fingerprint']['selected_objects']
 assert r['deps_fingerprint']['lean_binary_sha256']
 assert 'Running as unit:' in (E/(r['attempt']+'-launcher.log')).read_text()
 assert r['cgroup'].endswith('.scope')
final={}
for source in sorted(L.glob('Port10AUTH_*.lean')):
 name=source.name;h=sha(source)
 candidates=[r for r in rs if r['exit_status']==0 and r['source_hashes'].get(name)==h]
 assert candidates,name
 r=candidates[-1]
 assert all('sorryAx' not in a for a in r['print_axioms']),name
 assert not re.search(r'\b(sorry|admit|native_decide|maxRecDepth|maxHeartbeats)\b',source.read_text()),name
 final[name]={'sha256':h,'receipt':r['attempt'],'bytes':source.stat().st_size}
 for imported,depHash in r['deps_fingerprint']['direct_source_hashes'].items():
  p=L/(imported.replace('.','/')+'.lean')
  assert p.is_file() and sha(p)==depHash,(name,imported)
for kind in ['tail','tree','batch','tx1','both']:
 subprocess.run(['python3',str(T/f'Port10AUTH_{kind}_gen.py'),'--check'],cwd=R,check=True)
for script in T.glob('*.py'):compile(script.read_text(),str(script),'exec')
audit=rs[-1];assert audit['attempt']=='lean-064' and audit['exit_status']==0
allowed={'propext','Classical.choice','Quot.sound'}
for line in audit['print_axioms']:
 match=re.search(r'depends on axioms: \[([^\]]*)\]',line)
 assert match and set(match.group(1).split(', '))<=allowed,line
names={re.search(r"'([^']+)'",line).group(1) for line in audit['print_axioms']}
declared=set()
for source in L.glob('Port10AUTH_*.lean'):
 text=source.read_text();ns=re.search(r'^namespace (\S+)',text,re.M)
 if ns:
  declared.update(ns.group(1)+'.'+n for n in re.findall(r'^theorem (\w+)',text,re.M))
assert names==declared,(names^declared)
prior=[]
for job in ['port8effects','port9oracle']:
 p=R/f'evidence/{job}-20261024/manifest.json'
 expected=subprocess.check_output(['git','show','f8c9814c28:'+str(p.relative_to(R))],cwd=R)
 assert p.read_bytes()==expected
 prior.append({'path':str(p.relative_to(R)),'sha256':sha(p)})
changed=subprocess.check_output(['git','diff','--name-only','f8c9814c28'],cwd=R,text=True).splitlines()
untracked=subprocess.check_output(['git','ls-files','--others','--exclude-standard'],cwd=R,text=True).splitlines()
for path in changed+untracked:
 assert path.startswith(('evidence/port10auth-20261024/','tools/port10auth-20261024/','docs/research/100bit-spend-path-20261013/lean/Port10AUTH_')),path
for root in [E,T]:
 for p in root.rglob('*.json'):
  assert p.stat().st_size<=5_000_000,p
assessment={'base_revision':'f8c9814c2849fb273d9bc8ce5f381b2172947be7','source_revision':subprocess.check_output(['git','rev-parse','HEAD'],cwd=R,text=True).strip(),'source_tree_dirty':True,'final_sources':final,'prior_ledgers':prior,'external_cache_assessment':'Selected direct imported objects and companion hashes are re-pinned in every actual receipt; historical transitive cache provenance and P6 source/lowering/adoption evidence are reused. No coherent release rebuild or new ELF identity gate.','elf_pins_reference_only':{'default':'f8c0ec72621fd5029a97d796c4a3623d0dc44a8e7074122372f9872915d143d4','devnet':'63ad3e9cc096dcbb55b3ca7ac7c8e89e6a845796ab5e4f5b7d15db96f3784299','Pool':'121f3e29741f510e6dc42d0345fc3c36217600f0be337094855c4a9da2581548'},'new_identity_gate':False,'source_changes':'Only new job-prefixed formal modules, tools and evidence; no crates/programs/protocol/wire/features/security-contract changes.'}
(E/'source-assessment.json').write_text(json.dumps(assessment,indent=2)+'\n')
result={'status':'pass','attempts_counted':64,'actual_lean_runs':63,'prelean_rejections':1,'cumulative_attempts':160,'remaining':0,'final_source_count':len(final),'final_audit_reports':len(audit['print_axioms']),'unique_audited_theorems':len(names),'standard_axioms_only':True,'generator_checks':5,'caps_and_aggregate_reservations':'pass','source_dependency_hashes':'pass','prior_ledgers_unchanged':True,'no_shipped_source_changes':True,'no_full_manifest_replay':True,'resource_failures_retained': ['lean-040','lean-053'],'resource_failure_replacements':['lean-041/042: isolated scratch projection and symbolic log composition','lean-054: anchored source delimiter retains complete residual branches'],'premature_dependent_launch':'lean-033 rejected before Lean; counted conservatively with explicitly unavailable metrics'}
(E/'static-verification.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result))
