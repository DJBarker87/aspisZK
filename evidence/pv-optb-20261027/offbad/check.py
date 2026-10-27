#!/usr/bin/env python3
"""One focused private-root compile, with existing env-J runner and caps.
Does not modify a launcher, shared env, source, or object.
"""
import pathlib, subprocess, json, hashlib, shlex, sys, re, time
P=pathlib.Path(__file__).resolve().parent
H='dombarker@100.108.41.90'; B='/home/dombarker/project-offloads'; J=B+'/codex-pv-optb-20261027'
def remote(s): return subprocess.run(['ssh',H,s],capture_output=True,text=True)
def q(s): return shlex.quote(str(s))
a=int(sys.argv[1]); module=sys.argv[2]
assert 44600<=a<=44899
src=pathlib.Path('docs/research/v8-r0-zk-20261009/lean')/(module+'.lean')
assert module.startswith('R1Z/PV_OptB_')
assert not (P/f'launch-{a}.json').exists()
rev=subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip()
sha=hashlib.sha256(src.read_bytes()).hexdigest()
(P/f'launch-{a}.json').write_text(json.dumps(dict(attempt=a,target=module,source_revision=rev,source_sha256=sha))+'\n')
pre=remote(f'python3 {B}/codex-pv-l2-sim-20261026/reservation.py {J}/reservation-{a}.json > {J}/reservation-{a}.log 2>&1; cat {J}/reservation-{a}.json')
(P/f'reservation-{a}.log').write_text(pre.stderr+'\n'+pre.stdout)
if pre.returncode or not json.loads(pre.stdout)['allowed']: print(pre.stdout,pre.stderr); sys.exit(78)
subprocess.run(['ssh',H,f'mkdir -p {J}/lean-private/R1Z {J}/lean-objects/R1Z {J}/offbad; test ! -e {J}/offbad/out-{a}.log; test ! -e {B}/aspis-fs-generic-20261006/evidence/out-{a}.log'],check=True)
subprocess.run(['scp','-q',str(src),H+':'+J+'/lean-private/'+module+'.lean'],check=True)
cmd=f'systemd-run --user --scope --quiet --unit=pv-optb-{a} -p MemoryHigh=6G -p MemoryMax=8G -p MemorySwapMax=0 -p TasksMax=64 /usr/bin/time -v -o {J}/offbad/time-{a}.log timeout 900 python3 {B}/aspis-fs-generic-20261006/evidence/run2.py {B}/r1-privacy-build-integration-20261019/env/J.json {J}/lean-objects {J}/lean-private {J}/lean-objects/{module}.olean {J}/lean-private/{module}.lean 7000 > {J}/offbad/out-{a}.log 2>&1; echo exit=$? >> {J}/offbad/out-{a}.log; cat {J}/offbad/out-{a}.log; cat {J}/offbad/time-{a}.log'
r=remote(cmd)
subprocess.run(['scp','-q',H+':'+J+f'/offbad/out-{a}.log',H+':'+J+f'/offbad/time-{a}.log',str(P)],check=True)
o=(P/f'out-{a}.log').read_text(); t=(P/f'time-{a}.log').read_text()
def field(x):
 m=re.search(re.escape(x)+': (.*)',t); return m.group(1) if m else None
row=dict(attempt=a,target=module,source_revision=rev,source_sha256=sha,exit=int(re.search(r'^exit=(\d+)',o,re.M)[1]),wall=field('Elapsed (wall clock) time (h:mm:ss or m:ss)'),peak_rss_KiB=field('Maximum resident set size (kbytes)'),swap=field('Swaps'),axioms=re.findall(r"'[^'\n]+'(?: depends on axioms:\s*\[[^\]]*\]| does not depend on any axioms)",o),caps='MemoryHigh=6G MemoryMax=8G MemorySwapMax=0 TasksMax=64 Lean -M7000',routing='existing run2.py, env/J.json read-only, private source/object roots',deps='private objects first; original env-J read-only closure')
with (P/'receipts.jsonl').open('a') as f:f.write(json.dumps(row)+'\n')
rows=[json.loads(x) for x in (P/'receipts.jsonl').read_text().splitlines()]
(P/'TALLY.md').write_text(f'Lean {len(rows)}/100; Kani 0/4 (control only). Used IDs: '+', '.join(str(x['attempt']) for x in rows)+'. Audit IDs reserved: 44897–44899. No ID reuse.\n')
print(json.dumps(row)); print(o[-6000:]); sys.exit(row['exit'])
