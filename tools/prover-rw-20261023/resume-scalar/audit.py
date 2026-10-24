"""One focused packet/source audit; no proof/build/replay invocation."""
from pathlib import Path
import hashlib,json,re,subprocess,sys
D=Path(__file__).resolve().parent;ROOT=D.parents[2]
E=ROOT/'docs/research/100bit-spend-path-20261013/evidence/prover-rw-20261023/resume-scalar'
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
assert subprocess.check_output(['git','branch','--show-current'],cwd=ROOT,text=True).strip()=='codex/cx-prover-rw-20261023'
assert not subprocess.check_output(['git','diff','7e900bb534','--','crates','programs','tools/prover-rw-20261023/resume-p6'],cwd=ROOT)
changed=subprocess.check_output(['git','diff','--name-only','7e900bb534'],cwd=ROOT,text=True).splitlines()
assert all('/resume-scalar/' in x for x in changed),changed
s=(D/'proof/selected.rs').read_text();old=(D.parent/'resume-p6/compact/proof/selected.rs').read_text()
assert s==old.replace('ProverRwResumeP6','ProverRwResumeScalar')
m=json.loads((D/'source-map.json').read_text())
z=(D/'zeroize-instrumented.rs.txt').read_text();restored=z
for p in reversed(m['zeroize']['patches']):
 assert restored.count(p['after'])==1;restored=restored.replace(p['after'],p['before'])
assert restored==(D/'zeroize-original.rs.txt').read_text()
assert sha(D/'zeroize-original.rs.txt')==sha(D.parent/'resume-p6/compact/zeroize-original.rs.txt')
assert sha(D/'zeroize-instrumented.rs.txt')==m['zeroize']['instrumented_sha256']
g=(D/'getrandom-error-instrumented.rs.txt').read_text()
assert g.replace(m['getrandom']['after'],m['getrandom']['before'])==(D/'getrandom-error-original.rs.txt').read_text()
assert sha(D/'proof/selected.rs')==m['selected_sha256']
assert m['semantic_erasure_proved'] is False
array=next(p['after'] for p in m['zeroize']['patches'] if p['label']=='array typed observation')
observer=array[array.index('fn prover_rw_resume_scalar_observe'):]
assert all(x not in observer for x in ['while ','for ','copy_from_slice','[0u8;64]','Snapshot','unsafe','expect(','unwrap('])
assert observer.count('self[j]')==1 and observer.count('self[j + 32]')==1
assert 'j >= 32' in observer and 'N != 32 && N != 64' in observer
metadata=(D/'metadata.rs.txt').read_text()
assert all(x not in metadata for x in ['[u8;','[Event;','COUNT+=','COUNT +=','assert!','expect(','unwrap(','Drop for'])
assert '0 => { E0 = event; COUNT = 1; }' in metadata
assert '1 => { E1 = event; COUNT = 2; }' in metadata
assert '2 => { E2 = event; COUNT = 3; }' in metadata
assert '_ => { OVERFLOW = true; }' in metadata
assert 'J = (j % 32) as usize' in metadata
assert 'volatile_write(self, Z::default());\n        atomic_fence();' in z
assert 'self.iter_mut().zeroize();' in array
assert 'Some(*self)' in z
h=(D/'proof/lib.rs').read_text()
assert h.count('Ghost::initialize(')==1 and h.count('kani::assume(')==1
for t in ['let raw_j=kani::any::<u8>();','let nonce=kani::any::<[u8;32]>();','let post=kani::any::<[u8;64]>();','let entry=(kani::any::<u8>()%16) as usize;','let repr=kani::any::<i32>();','kani::assume(code.is_some());','assert_eq!(original,instrumented);','assert_eq!(Ghost::events(),ghost_after);','assert_eq!(Ghost::coordinate(),j);']:assert t in h,t
assert h.count('#[kani::stub(')==1 and '#[kani::stub(getrandom::fill,fill_boundary)]' in h
obs=(D/'proof/observe.rs').read_text();assert obs.index('phase(success);')<obs.index('drop(owner);')
assert obs.count('drop(owner);')==1
roles=json.loads((D/'source-role-map.json').read_text());assert roles['source_sha256']==sha(D/'proof/selected.rs')
for row in roles['bindings'].values():
 assert s[row['byte_start']:row['byte_end']]==row['text']
 assert hashlib.sha256(row['text'].encode()).hexdigest()==row['sha256']
reused=json.loads((E/'reused-bindings.json').read_text())
for path,digest in reused['input_sha256'].items():assert sha(ROOT/path)==digest
assert reused['success_obstruction']['recorded_branch']['statements']==[]
assert reused['actual_extraction_invocations']==0
receipt=json.loads((E/'packet/rust001/receipt-summary.json').read_text())
admission=json.loads((E/'packet/rust001/admission-before.json').read_text())
assert receipt['exit_status']==78 and receipt['actual_invocations']==0 and receipt['Kani_invocations']==0
assert admission['allowed'] is False and admission['reserve_check'] is False
assert admission['projected_reserved_bytes']<55*2**30
assess=json.loads((E/'denial-source-assessment.json').read_text())
assert not assess['go_exists'] and not assess['target_started'] and assess['compiler_invocations']==0
# Do not attribute the denied snapshot to the final source or a compiler run.
source_differences={p:dict(denied=h,final=sha(D/p)) for p,h in assess['job_source_pins_at_denial'].items() if (D/p).exists() and sha(D/p)!=h}
for package in json.loads((E/'package-identity.json').read_text()):
 assert [p for p in package['upstream_files'] if package['upstream_files'][p]!=package['job_files'][p]]==[package['changed_path']]
original=json.loads((E/'erasure-package-identity.json').read_text())
assert [p for p in original['upstream_files'] if original['upstream_files'][p]!=original['job_files'][p]]==['Cargo.toml']
lean=[]
for attempt in [239,240,241,242]:
 p=E/f'lean-{attempt}/receipt.json';r=json.loads(p.read_text());assert r['swaps']==0
 assert r['exit_status']==(1 if attempt==240 else 0)
 if attempt!=240:
  assert r.get('accepted',r['exit_status']==0) and r['source_unchanged'] and r['dependencies_unchanged']
  assert 'sorryAx' not in '\n'.join(r['print_axioms'])
  for line in r['print_axioms']:
   match=re.search(r'axioms: \[([^\]]*)\]',line)
   if match:assert set(x.strip() for x in match[1].split(','))<={'propext','Classical.choice','Quot.sound'}
  assert sha(D/'lean'/(r['module']+'.lean'))==r['source_sha256']
 lean.append({k:r.get(k) for k in ['attempt','module','command','exit_status','wall_seconds','target_wall_seconds','peak_rss_bytes','swaps','source_revision','source_sha256','dependency_fingerprint','print_axioms','accepted']})
assert len(lean)==4
for p in E.rglob('*.json'):assert p.stat().st_size<=5_000_000,p
# Final packet source/dependency hashes; omit compiled objects entirely.
inputs={str(p.relative_to(ROOT)):sha(p) for base in [D,E] for p in sorted(base.rglob('*')) if p.is_file() and '__pycache__' not in p.parts and p.name not in ['audit.json','audit.stdout','audit.time','audit-receipt.json']}
out=dict(schema='ProverRwResumeScalar-focused-audit-v1',source_revision=subprocess.check_output(['git','rev-parse','HEAD'],cwd=ROOT,text=True).strip(),command=sys.argv,input_sha256=inputs,denied_snapshot_vs_final=source_differences,structural_payload=dict(old_bytes=384,new_bytes=12,reduction_factor=32,old_Ok_observer_reads=256,new_Ok_observer_reads=8,observation_loops=0),lean_results=lean,budgets=dict(entry=dict(Kani=59,Lean=236,extraction=54,backend=15,Rust=0,ELF=0),exit=dict(Kani=59,Lean=240,extraction=54,backend=15,Rust_charged_admission_attempt=1,ELF=0),actual_invocations=dict(Kani=0,Lean=4,Rust_compiler=0,Charon=0,Aeneas=0,backend=0,ELF=0),Rust_admission_denials=1,Lean_pin_generation_failures=2,last_Kani_reserved=True,full_manifest=0),semantic_erasure_proved=False,native_source_role_closure=False,source_inspected_argument='RELATION.md; standard-axiom finite arithmetic/coverage only',print_axioms='Full Lean axioms in lean_results; N/A for this Python audit',claim='Source/packet structural audit only; native relation, world/controller/experiment and both deployed targets remain unestablished')
Path(sys.argv[1]).write_text(json.dumps(out,indent=2)+'\n')
print('PASS scalar source/packet audit; observer payload384->12; native erasure/roles/world/controller remain open')
