"""Bind each Rust gate's cumulative host delta and unchanged source prefix."""
from pathlib import Path
import subprocess,json,hashlib
E=Path(__file__).resolve().parent.parent
prior=E.parent/'prover-commit22-20261021'
host='dombarker@100.108.41.90'
H='/home/dombarker/project-offloads/codex-cx-prover-commit23-20261021'
P=H.replace('commit23-','commit22-')
sha=lambda b:hashlib.sha256(b).hexdigest()
get=lambda root,p:subprocess.check_output(['ssh',host,'cat '+root+'/src/'+p])
sim='crates/aspis-r1-cost-probe/src/sim.rs'
baseline=get(P,sim)
old=json.loads((prior/'source-prefix-binding.json').read_text())
assert sha(baseline)==old['files'][0]['full_instrumented_sha256']
tls=(E/'harness/tls23.rs').read_bytes()
tls1=tls.replace(b"fn single_with<T: 'static, F, R>(_: &std::thread::LocalKey<T>, f: F) -> R",b'fn single_with<F, R>(_: &std::thread::LocalKey<Trace>, f: F) -> R').replace(b'F: FnOnce(&T) -> R',b'F: FnOnce(&Trace) -> R').replace(b'&*(core::ptr::addr_of!(SLOT) as *const T)',b'&*core::ptr::addr_of!(SLOT)')
(E/'harness/tls23-v1.rs.txt').write_bytes(tls1)
tree=(E/'harness/tree23.rs').read_bytes()
leaf=(E/'harness/tree23leaf.rs').read_bytes()
retained=(E/'harness/tree23retained.rs').read_bytes()
programmed=(E/'harness/tls_programmed23.rs').read_bytes()
deltas={'tls-single-v1':tls1,'tls-single-v2':tls,
 'tree-insert-v1':tls+tree,'tree-get-v1':tls+tree,'tree-iter-v1':tls+tree,
 'tree-insert-leaf-v2':tls+tree+leaf,
 'tree-insert-retained-v3':tls+tree+leaf+retained,
 'tls-programmed-v1':tls+tree+leaf+retained+programmed}
old_inputs=json.loads((prior/'tls-append-v1-inputs.json').read_text())['source_hashes']
rows=[]
for name,delta in deltas.items():
 manifest=json.loads((E/(name+'-inputs.json')).read_text())
 assert manifest['source_revision']=='cb9372b8f'
 assert sha(baseline+delta)==manifest['source_hashes'][sim],name
 assert all(h==old_inputs[p] for p,h in manifest['source_hashes'].items() if p!=sim),name
 rows.append(dict(name=name,sim_sha256=sha(baseline+delta),delta_sha256=sha(delta),delta_bytes=len(delta),all_other_source_hashes_unchanged=True))
remote=get(H,sim);assert remote==baseline+deltas['tls-programmed-v1']
files=[]
for f in ['sim.rs','r1_wire.rs','transcript.rs','trace.rs','sampler.rs']:
 path='crates/aspis-r1-cost-probe/src/'+f
 original=Path(path).read_bytes();current=get(H,path);projected=current;inherited=b''
 if f=='sim.rs':
  start=current.index(b'// Owned reference for exactly one source Coins::coin transition.')
  end=current.index(b'// Proof-only owned references.',start)
  inherited=current[start:end];assert sha(inherited)==old['files'][0]['inherited_coin18_sha256']
  projected=current[:start]+current[end:]
 assert projected.startswith(original),f
 files.append(dict(file=path,production_sha256=sha(original),production_bytes=len(original),full_instrumented_sha256=sha(current),full_bytes=len(current),production_prefix_matches_after_inherited_projection=True,inherited_coin18_sha256=sha(inherited) if inherited else None))
(E/'source-prefix-binding.json').write_text(json.dumps(dict(base='cb9372b8f',source_revision=subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip(),baseline_evidence=str(prior/'source-prefix-binding.json'),baseline_sim_sha256=sha(baseline),files=files,rust_inputs=rows,scope='Host-only cfg(kani) deltas, cumulative hashes reconstructed for every gate; no local shipped file changes'),indent=2)+'\n')
print('PASS: all eight cumulative Rust gate sources and unchanged source prefixes')
