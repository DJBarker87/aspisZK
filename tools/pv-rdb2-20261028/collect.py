from pathlib import Path
import subprocess,json,shlex,lzma,hashlib
R=Path(__file__).resolve().parents[2];E=R/'evidence/pv-rdb2-20261028';D='/home/dombarker/project-offloads/codex-pv-rdb2-20261028';H='dombarker@100.108.41.90';g='/home/dombarker/project-offloads/codex-cx-prover-rw-20261023/src/tools/prover-rw-20261023/native-entropy'
# Receipt recovery is read-only and must never re-submit a compiler.
for suite in ['rows','arithmetic','multilinear','leaves','sum','sampler','weights','sha','ct']:
 kind='dep' if suite in ['sha','ct'] else 'project';src=f'{D}/classify-{kind}-{suite}';dest=E/('native-'+suite)
 for name in ['inputs.json','Cargo.toml.txt','metadata.json']:
  b=subprocess.check_output(['ssh',H,'cat '+shlex.quote(src+'/'+name)])
  if name=='metadata.json':(dest/(name+'.xz')).write_bytes(lzma.compress(b));(dest/(name+'.sha256')).write_text(hashlib.sha256(b).hexdigest()+'\n')
  else:(dest/name).write_bytes(b)
 inp=json.loads((dest/'inputs.json').read_text());j=json.loads((dest/'receipt.json').read_text());j.update(resolved_features=inp['features'],profile=inp['profile'],toolchain='rustc1.94.1',deployed_source_preflight='../source-identity.json; ../deployed-sources-live.json',fixture_inputs='inputs.json',evidence_class='finite same-input native validation; no universal native law',axioms='N/A native Rust')
 (dest/'receipt.json').write_text(json.dumps(j,indent=2)+'\n')
 if kind=='project':
  b=subprocess.check_output(['ssh',H,'cat '+shlex.quote(src+'/fixture.rs.txt')]);(dest/'fixture.rs.txt').write_bytes(b)
for row in ['V229','V230','V231','V238','V239','V240','V247','V256','V257','V258','V259']:
 b=subprocess.check_output(['ssh',H,'cat '+D+'/'+row+'-source-gate.json']);(E/(row+'-source-gate.json.xz')).write_bytes(lzma.compress(b));(E/(row+'-source-gate.sha256')).write_text(hashlib.sha256(b).hexdigest()+'\n')
b=subprocess.check_output(['ssh',H,'cat '+D+'/classify-structural/results.json']);(E/'wrapper-structural/results.json').write_bytes(b)
for n in ['source-gates','wrapper-structural']:
 q=E/n/'receipt.json';j=json.loads(q.read_text());j.update(profile='release opt3 debug_assertions=false overflow_checks=false panic=unwind; selected-source audit, no compiler',resolved_features_reference='../native-rows/receipt.json (client/project); ../native-sha/receipt.json and ../native-ct/receipt.json (dependency wrappers)',toolchain='rustc1.94.1 source selection; no Rust compilation in this scope',axioms='N/A Python source gate');q.write_text(json.dumps(j,indent=2)+'\n')
# Exact compiler version and input script hashes are configuration evidence.
code='''from pathlib import Path
import hashlib,json,subprocess
D=Path(DIR)
version=subprocess.check_output(['/home/dombarker/.cargo/bin/rustup','run','1.94.1','rustc','-vV'],text=True)
print(json.dumps(dict(rustc=version,scripts={p.name:hashlib.sha256(p.read_bytes()).hexdigest() for p in D.glob('*.py')})))
'''.replace('DIR',repr(D))
b=subprocess.check_output(['ssh',H,'python3 -c '+shlex.quote(code)]);(E/'runtime-configuration.json').write_bytes(b)
print('Recovered exact inputs/features/metadata and all per-row source-gate results')
