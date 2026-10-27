"""Focused proof tooling using the unchanged host gate and pinned tool executables."""
from pathlib import Path
import subprocess,sys,shlex,json,time,re,hashlib
r=Path(__file__).resolve().parents[2];e=r/'evidence/pv-join-20261026/resume5';host='dombarker@100.108.41.90';own='/home/dombarker/project-offloads/codex-pv-join-20261026';name=sys.argv[1];kind=sys.argv[2]
dest=f'{own}/{name}';local=e/name;local.mkdir(exist_ok=True)
assert not (local/'target.json').exists()
def ssh(c):return subprocess.run(['ssh','-o','BatchMode=yes',host,c],text=True,capture_output=True)
q=ssh(f'mkdir -p {dest} {own}/direct5; python3 /home/dombarker/project-offloads/codex-cx-s2x-20261023/S2X_reservation.py {dest}/admission.json > {dest}/admission.log 2>&1; code=$?; cat {dest}/admission.log; exit $code')
for f in ['admission.json','admission.log']:(local/f).write_text(ssh(f'cat {dest}/{f}').stdout)
if q.returncode:print(q.stdout,q.stderr);sys.exit(q.returncode)
assert json.loads((local/'admission.json').read_text())['allowed']
for f in ['Cargo.toml','lib.rs']:
 p=r/'tools/pv-join-20261026/direct5'/f;subprocess.run(['scp',str(p),host+f':{own}/direct5/{f}'],check=True,capture_output=True);(local/(f+'.txt')).write_bytes(p.read_bytes())
env=['env','PATH=/home/dombarker/.cargo/bin:/usr/local/bin:/usr/bin:/bin',f'CARGO_TARGET_DIR={own}/pole-target']
if kind in ['list','kani']:
 args=env+['cargo','kani',*(['list','--format','json'] if kind=='list' else ['--harness',sys.argv[3],*(['--no-overflow-checks'] if len(sys.argv)>4 and sys.argv[4]=='release-wrap' else []),'--solver','kissat','--output-format','terse','-j','4']),*([] if kind=='list' else ['--manifest-path',f'{own}/direct5/Cargo.toml','--lib'])]
elif kind=='rust':
 args=env+['cargo','run','--release','--offline','--manifest-path',f'{own}/direct5/Cargo.toml','--bin','poly-preflight','--jobs','4']
elif kind=='charon':
 args=env+['RUSTUP_TOOLCHAIN=nightly-2026-06-01','RUSTFLAGS=--cfg kani --cfg pv_join_extract','/home/dombarker/project-offloads/codex-pv-cb-20261026/pinned-tools/charon','cargo','--preset','aeneas','--mir','built','--rustc-arg=--cfg=kani','--rustc-arg=--cfg=pv_join_extract','--sysroot','default','--start-from',('pv_join_direct5::'+(sys.argv[3] if len(sys.argv)>3 else 'evaluate')),'--include','pv_join_direct5::*','--include','aspis_core::field::*','--opaque','aspis_core::*::*::*::call_once','--opaque','aspis_core::*::*::*::*::call_once','--dest-file',f'{own}/direct5.llbc','--','--manifest-path',f'{own}/direct5/Cargo.toml','--release','--offline','--lib','--jobs','4']
elif kind=='aeneas':
 args=['/home/dombarker/project-offloads/codex-pv-cb-20261026/pinned-tools/aeneas','-sequential','-no-progress-bar','-abort-on-error','-strict-joins','-backend','lean','-namespace','PV_Join_Direct5Source','-dest',f'{own}/direct5-generated','-split-files','-emit-json',f'{own}/direct5.llbc'];assert ssh(f'mkdir -p {own}/direct5-generated').returncode==0
else:raise ValueError(kind)
x=dict(target=args,kind=kind,source_revision=subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip(),caps=dict(MemoryHigh='6G',MemoryMax='8G',MemorySwapMax=0,TasksMax=64),expected_time='symbolic proof of the named harness' if kind=='kani' else 'focused source extraction or harness listing',optimized_profile='dev opt-level=3, release opt-level=3',print_axioms='N/A; Lean closure separately audited')
(local/'target.json').write_text(json.dumps(x,indent=2)+'\n')
cmd=['systemd-run','--user','--scope','-p','MemoryHigh=6G','-p','MemoryMax=8G','-p','MemorySwapMax=0','-p','TasksMax=64','/usr/bin/time','-v','-o',f'{dest}/time.log','timeout','240',*args]
start=time.monotonic();out=ssh(f'cd {own}/direct5 && '+shlex.join(cmd)+f' > {dest}/output.log 2>&1');(local/'transport.log').write_text(out.stdout+out.stderr)
for f in ['output.log','time.log']:(local/f).write_text(ssh(f'cat {dest}/{f}').stdout)
tim=(local/'time.log').read_text();x.update(exit=out.returncode,wall_seconds=time.monotonic()-start,peak_rss_kib=re.findall(r'Maximum resident set size \(kbytes\):\s*(\d+)',tim),swaps=re.findall(r'Swaps:\s*(\d+)',tim));(local/'receipt.json').write_text(json.dumps(x,indent=2)+'\n')
print(name,'exit',out.returncode,flush=True);print((local/'output.log').read_text()[-2000:])
if kind=='aeneas' and not out.returncode:
 for f in ['Funs.lean','Types.lean','translation.json']:
  p=ssh(f'cat {own}/direct5-generated/{f}');(local/f).write_text(p.stdout)
sys.exit(out.returncode)
