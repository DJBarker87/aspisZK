from pathlib import Path
import json,subprocess,sys,re,hashlib,shlex
E=Path(__file__).resolve().parent;R=E.parents[1];H='dombarker@100.108.41.90';B='/home/dombarker/project-offloads/codex-pv-inv-20261027/inv3-kani'
def remote(c):return subprocess.run(['ssh',H,c],capture_output=True,text=True)
tally=json.loads((E/'TALLY.json').read_text());i=tally['kani_charged']+1;assert i<=6;name=sys.argv[1];q=E/f'K{i:02}';q.mkdir();src=E/'PV_Inv_control.rs'
remote(f'mkdir -p {B}')
r=remote(f'python3 /home/dombarker/project-offloads/codex-cx-s2x-20261023/S2X_reservation.py {B}/K{i:02}-reservation.json > {B}/K{i:02}-barrier.log 2>&1');z=remote(f'cat {B}/K{i:02}-reservation.json');(q/'admission.json').write_text(z.stdout);(q/'admission.log').write_text(remote(f'cat {B}/K{i:02}-barrier.log').stdout)
if not json.loads(z.stdout)['allowed']:sys.exit(78)
subprocess.run(['scp','-q',str(src),H+':'+B+'/'],check=True)
cmd=f'cd {B} && systemd-run --user --scope --quiet -p MemoryHigh=6G -p MemoryMax=8G -p MemorySwapMax=0 -p TasksMax=64 /usr/bin/time -v -o K{i:02}-time.log timeout 180 taskset --cpu-list 0-3 /home/dombarker/.cargo/bin/kani PV_Inv_control.rs --harness {shlex.quote(name)} -j 4 --output-format terse > K{i:02}-out.log 2>&1; code=$?; echo $code > K{i:02}-exit.txt'
r=remote(cmd)
for n,h in [('out.log','out.log'),('time.log','time.log'),('exit.txt','exit.txt')]: (q/n).write_text(remote(f'cat {B}/K{i:02}-{h}').stdout)
t=(q/'time.log').read_text();o=(q/'out.log').read_text()
def val(p):
 m=re.search(p,t);return m[1].strip() if m else None
code=int((q/'exit.txt').read_text());tally['kani_charged']=i;(E/'TALLY.json').write_text(json.dumps(tally,indent=2)+'\n')
d=dict(target=name,command=cmd,exit=code,source_revision=subprocess.check_output(['git','rev-parse','HEAD'],cwd=R,text=True).strip(),source_sha256=hashlib.sha256(src.read_bytes()).hexdigest(),wall=val(r'Elapsed \(wall clock\) time \(h:mm:ss or m:ss\): (.+)'),peak_rss_kib=val(r'Maximum resident set size \(kbytes\): (\d+)'),swaps=val(r'Swaps: (\d+)'),axioms='N/A: Kani',scope={'MemoryHigh':'6G','MemoryMax':'8G','MemorySwapMax':0,'TasksMax':64},expected_work='Kani translation and named bounded structural control assertion; no chained field arithmetic',claim='control slice only; no whole-function or source arithmetic equivalence')
(q/'receipt.json').write_text(json.dumps(d,indent=2)+'\n');print(i,name,code,o[-2000:],flush=True);sys.exit(code)
