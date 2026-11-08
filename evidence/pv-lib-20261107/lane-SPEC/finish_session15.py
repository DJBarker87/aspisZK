"""Run one focused module with the retained task-local launcher; retain all evidence."""
import subprocess,pathlib,json,sys
L=pathlib.Path(__file__).resolve().parent;R=L.parents[2]
H='dombarker@100.108.41.90';P='/home/dombarker/project-offloads/codex-pv-lib-spec-20261107'
m=sys.argv[1];a=int(sys.argv[2]);c=sys.argv[3] if len(sys.argv)>3 else 'w3'
p=R/'lean'/(m+'.lean')
subprocess.run(['scp',str(p),f'{H}:{P}/sources/'],check=True)
subprocess.run(['ssh',H,'STREAMB_SLOTS=3 /home/dombarker/streamb-slots/turn.sh'],check=True)
rev=subprocess.check_output(['git','rev-parse','HEAD'],cwd=R,text=True).strip()
with (L/f'launch-{a}.log').open('w') as out:
 r=subprocess.run(['ssh',H,f'python3 {P}/host_attempt_s15.py {a} {m} {rev} {c}'],stdout=out,stderr=subprocess.STDOUT)
subprocess.run(['scp',f'{H}:{P}/evidence/*-{a}.*',str(L)],check=True)
rp=json.loads((L/f'receipt-{a}.json').read_text());print(json.dumps({k:rp[k] for k in ['attempt','target','exit','wall','peak_rss_kbytes','swaps'] if k in rp}),flush=True)
if r.returncode or not rp.get('accepted'):
 import lzma
 (L/f'failed-{a}.lean.xz').write_bytes(lzma.compress(p.read_bytes()))
 print((L/f'out-{a}.log').read_text()[:14000]);sys.exit(1)
assert not any('sorryAx' in s for s in rp['axioms_summary_based'])
with (L/'SESSION15.md').open('a') as f:f.write(f'\n{m} compiled {a}, cohort {c}: exit0, wall {rp["wall"]}, peak {rp["peak_rss_kbytes"]}KiB, swap {rp["swaps"]}; source {rev}; standard summary axioms only.\n')
subprocess.run(['git','add','--sparse',str(p),str(L)],cwd=R,check=True)
subprocess.run(['git','commit','-m',f'Validate {m.removeprefix("PV_LIB_SPEC_")}'],cwd=R,check=True,stdout=subprocess.DEVNULL)
