from pathlib import Path
import subprocess,hashlib,json,sys
from run import H,run
mode=sys.argv[1];assert mode in ['byte-positive','byte-negative','matrix-linear','bit-positive','bit-negative','iterator-positive','iterator-negative','format-positive','format-negative','format-placeholder-positive','format-placeholder-negative']
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
toolchain=subprocess.check_output(['/home/dombarker/.cargo/bin/rustc','+1.94.1','-vV'],text=True)
cmd=['/home/dombarker/.cargo/bin/rustc','+1.94.1','--edition=2021','-C','opt-level=3','-C','overflow-checks=off','-C','debug-assertions=off','-A','dead_code','-C','link-arg=-Wl,--threads=4']
if mode=='matrix-linear' or mode.startswith('iterator-'):
 B=H.parent/'codex-pv-b3p6-20261028';x=json.loads((B/'features227-resume4.json').read_text());features=next(n['features']for n in x['validation']['nodes']if n['name']=='aspis-core')
 for feature in features:cmd+=['--cfg','feature="'+feature+'"']
 binary=H/('matrix-linear' if mode=='matrix-linear' else 'iterator-native')
 cmd+=[str(H/('matrix/main_linear.rs' if mode=='matrix-linear' else 'matrix/main_iter.rs')),'-o',str(binary)];inputs={str(p.relative_to(H)):sha(p)for p in(H/'matrix').rglob('*.rs')};nodes=x['validation']['nodes']
else:
 name='format_error_native.rs' if mode.startswith('format-') else ('bit_counts_native.rs' if mode.startswith('bit-') else 'byte_eq_native.rs')
 binary=H/('format-error-native' if mode.startswith('format-') else ('bit-counts-native' if mode.startswith('bit-') else 'byte-eq-native'))
 cmd+=[str(H/name),'-o',str(binary)];inputs={name:sha(H/name)};nodes='core/std from pinned 1.94.1; no external dependency'
record=dict(mode=mode,toolchain=toolchain,profile=dict(opt_level=3,overflow_checks=False,debug_assertions=False),input_hashes=inputs,resolved_nodes=nodes,evidence_class='finite validation; compiler/source-to-shipped-code boundary V370 retained')
(H/(mode+'-inputs.json')).write_text(json.dumps(record,indent=2)+'\n')
if mode.endswith('-negative'):cmd=[str(binary),'--negative']
else:
 (H/(mode+'-command.json')).write_text(json.dumps(dict(compile=cmd,run=[str(binary)])))
 cmd=['python3',str(H/'native_extra_gate.py'),mode]
r=run('native-'+mode,cmd,'optimized compilation then one named byte-equality or full matrix observation; no elimination/proof generation')
if binary.exists():(H/(mode+'-binary.json')).write_text(json.dumps(dict(sha256=sha(binary),bytes=binary.stat().st_size),indent=2)+'\n')
raise SystemExit(r)
