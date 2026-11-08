import subprocess,pathlib,json,sys
L=pathlib.Path('evidence/pv-lib-20261107/lane-SPEC');H='dombarker@100.108.41.90';P='/home/dombarker/project-offloads/codex-pv-lib-spec-20261107'
m=sys.argv[1];a=int(sys.argv[2]);c=sys.argv[3] if len(sys.argv)>3 else 'w3'
p=pathlib.Path('lean')/(m+'.lean')
def run(args,**kw):return subprocess.run(args,check=True,**kw)
run(['scp',str(p),f'{H}:{P}/sources/'])
run(['ssh',H,'STREAMB_SLOTS=3 /home/dombarker/streamb-slots/turn.sh'])
rev=subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip()
r=subprocess.run(['ssh',H,f'python3 {P}/host_attempt_semantic.py {a} {m} {rev} {c}'],stdout=subprocess.DEVNULL)
run(['scp',f'{H}:{P}/evidence/*-{a}.*',str(L)])
rp=json.loads((L/f'receipt-{a}.json').read_text());print(json.dumps({k:rp[k] for k in ['attempt','target','exit','wall','peak_rss_kbytes','swaps'] if k in rp}),flush=True)
if r.returncode or not rp.get('accepted'):sys.exit(1)
assert not any('sorryAx' in s for s in rp['axioms_summary_based'])
with (L/'SESSION5.md').open('a') as f:f.write(f'\n{m} compiled{a}, cohort{c}: exit0, wall{rp["wall"]}, peak{rp["peak_rss_kbytes"]}KiB, swap{rp["swaps"]}; standard summary axioms only. Statement only.\n')
run(['git','add','--sparse',str(p),str(L)])
run(['git','commit','-m',f'State and validate {m.removeprefix("PV_LIB_SPEC_")}'],stdout=subprocess.DEVNULL)
