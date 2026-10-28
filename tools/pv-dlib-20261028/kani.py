"""One bounded, no-stub native/reference gate in the private proof workspace."""
from pathlib import Path
import subprocess,json,sys
R=Path(__file__).resolve().parents[2];E=R/'evidence/pv-dlib-20261028';D='/home/dombarker/project-offloads/codex-pv-dlib-20261028'
name,harness=sys.argv[1:3];assert name.startswith('kani-')
t=json.loads((E/'TALLY.json').read_text());assert len(t['kani_charged'])<6 and name not in t['kani_charged']
cmd=['timeout','900','taskset','--cpu-list','0-3','env','PATH=/home/dombarker/.cargo/bin:/usr/local/bin:/usr/bin:/bin','CARGO_BUILD_JOBS=4','CARGO_PROFILE_DEV_OPT_LEVEL=3','CARGO_PROFILE_DEV_OVERFLOW_CHECKS=false','RUSTFLAGS=--cfg kani','CARGO_TARGET_DIR='+D+'/kani-target','cargo','kani','--manifest-path',D+'/native-proof/Cargo.toml','--lib','--exact','--harness',harness,'--solver','kissat','--output-format','terse','-j','4','-Z','unstable-options','--cbmc-args','--unwinding-assertions']
r=subprocess.run([sys.executable,str(R/'tools/pv-dlib-20261028/scope.py'),name,'optimized native/library compilation then bounded control and byte plumbing equivalence; no chained field arithmetic, no compression evaluation',*cmd])
p=E/name/'receipt.json'
if p.exists():
 j=json.loads(p.read_text());j['native_link_class']='P6 no-stub bounded library/reference; observers only, original library prefixes unchanged';j['bound']=('prefix position <64, input length <=129, arbitrary u64 counter, unwind 196' if 'update' in harness else 'position <64, arbitrary u64 bit length, unwind 70' if 'padding' in harness else 'constructor; unwind 70');p.write_text(json.dumps(j,indent=2)+'\n')
 t=json.loads((E/'TALLY.json').read_text());t['kani_charged'].append(name);(E/'TALLY.json').write_text(json.dumps(t,indent=2)+'\n')
sys.exit(r.returncode)
