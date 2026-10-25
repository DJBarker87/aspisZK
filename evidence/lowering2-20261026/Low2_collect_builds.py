#!/usr/bin/env python3
"""Hash actual private build inputs, compiler dependency files and tool binaries."""
import hashlib,json,re,subprocess
from pathlib import Path
H=Path('/home/dombarker/project-offloads/codex-cx-lowering2-20261026')
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
x=json.loads((H/'source-inputs.json').read_text())
source_checks=[{'path':p,'expected_sha256':s,'actual_sha256':sha(H/'src'/p)} for p,s in x['files'].items()]
assert all(r['expected_sha256']==r['actual_sha256'] for r in source_checks)
rows=[]
for mode,build in [('default','build-default-v2'),('devnet','build-devnet-v1'),('pool','build-pool-v1')]:
 b=H/build;cmd=json.loads((b/'command.json').read_text());rec=json.loads((b/'receipt/receipt.json').read_text())
 # The reused capped launcher embeds a historical revision. Preserve it verbatim,
 # and bind the actual private source revision here rather than relabelling it.
 rec['actual_build_source_revision']=x['source_revision']
 artifact=json.loads((b/'artifact-comparison.json').read_text());assert artifact['byte_identical']
 target=H/('sbf-target-pool' if mode=='pool' else 'sbf-target-verifier')
 name='aspis_pool' if mode=='pool' else 'aspis_r1_cost_probe_program'
 d=target/'sbpf-solana-solana/release'/(name+'.d');raw=d.read_text()
 deps=raw.split(': ',1)[1].strip().split()
 local=[];generated=[]
 for dep in deps:
  p=Path(dep).resolve()
  if p.is_relative_to(H/'src'):
   rel=str(p.relative_to(H/'src'));assert sha(p)==x['files'][rel];local.append({'path':rel,'sha256':sha(p)})
  else:generated.append({'path':str(p),'sha256':sha(p),'bytes':p.stat().st_size})
 compiler=[]
 for p in sorted((b/'diagnostics').glob('*.command.json')):
  args=json.loads(p.read_text());rustc=Path(args[0]);compiler.append({'crate':p.stem,'args':args,'command_sha256':sha(p),'rustc_sha256':sha(rustc),'rustc_version':subprocess.check_output([str(rustc),'-vV'],text=True)})
 rows.append({'mode':mode,'build':build,'command':cmd,'receipt':rec,'artifact':artifact,'depfile':{'path':str(d),'sha256':sha(d),'text':raw},'repository_compiler_inputs':local,'generated_compiler_inputs':generated,'compiler_invocations':compiler})
# Source membership is inferred from compiler depfiles, not all inventoried files.
# default/devnet dependency file is shared by identically featured builds; source
# bytes and commands are retained. Program ID environment is separately pinned.
version='/home/dombarker/.local/share/solana/install/releases/3.1.13/solana-release/bin/cargo-build-sbf'
out={'source_revision':x['source_revision'],'source_checks':source_checks,'builds':rows,'toolchain':{'cargo_build_sbf_sha256':sha(Path(version)),'version':subprocess.check_output([version,'--version'],text=True)},'depfile_note':'Default/devnet share identical feature set and private Cargo target. Final compiler depfile covers both; program IDs differ only in pinned environment. No repository bytes changed between builds.'}
(H/'Low2_build_manifest.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps({'source_files':len(source_checks),'builds':[{ 'mode':r['mode'],'sha256':r['artifact']['sha256'],'compiler_inputs':len(r['repository_compiler_inputs'])} for r in rows]}))
