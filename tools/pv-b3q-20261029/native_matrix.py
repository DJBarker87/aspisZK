"""Optimized, source-identical native matrix observation; finite validation."""
from pathlib import Path
import subprocess,json,hashlib,sys
from run import H,run
mode=sys.argv[1];assert mode in ['positive','negative'];P=H/'matrix';B=H.parent/'codex-pv-b3p6-20261028'
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
old=json.loads((B/'features227-resume4.json').read_text())
# The isolated field cone has no dependency calls: its methods call only core
# primitives and the exact local ct/wide_exact modules. Preserve every active
# feature of aspis-core, rather than the proof harness package's feature list.
nodes=old['validation']['nodes'];node=next(n for n in nodes if n['name']=='aspis-core');features=node['features']
record=dict(mode=mode,toolchain=subprocess.check_output(['/home/dombarker/.cargo/bin/rustc','+1.94.1','-vV'],text=True),resolved_deployed_nodes=nodes,field_crate_features=features,profile=old['profile'],inputs={str(p.relative_to(H)):sha(p)for p in P.rglob('*.rs')},compiler_boundary='V370 / D381,D386 retained',evidence_class='finite validation of exact deployed-source matrix observation; source-to-shipped-code remains V370')
(H/f'matrix-{mode}-inputs.json').write_text(json.dumps(record,indent=2)+'\n')
if mode=='positive':
 cmd=['/home/dombarker/.cargo/bin/rustc','+1.94.1','--edition=2021','-C','opt-level=3','-C','overflow-checks=off','-C','debug-assertions=off','-A','dead_code','-C','link-arg=-Wl,--threads=4']
 for feature in features:cmd+=['--cfg','feature="'+feature+'"']
 cmd +=[str(P/'main.rs'),'-o',str(H/'matrix-native')]
 # Single capped scope, compile and run; no arithmetic proof generation.
 (H/'native-command.json').write_text(json.dumps(cmd))
 cmd=['python3',str(H/'native_matrix_gate.py')]
else:cmd=[str(H/'matrix-native'),'--negative']
r=run('native-matrix-'+mode,cmd,'optimized Rust compilation and one named 3x3 matrix comparison; no elimination')
if(H/'matrix-native').exists():(H/f'matrix-{mode}-binary.json').write_text(json.dumps(dict(sha256=sha(H/'matrix-native'),bytes=(H/'matrix-native').stat().st_size),indent=2)+'\n')
raise SystemExit(r)
