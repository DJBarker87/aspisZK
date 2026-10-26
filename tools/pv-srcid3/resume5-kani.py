#!/usr/bin/env python3
"""One reserved, optimized, capped Kani invocation; no automatic queue."""
import datetime,json,pathlib,shlex,subprocess,sys,time
root=pathlib.Path(__file__).resolve().parents[2];e=root/'evidence/pv-srcid3-20261026'
host='dombarker@100.108.41.90';job='/home/dombarker/project-offloads/codex-pv-srcid-20261026'
name,harness,seconds=sys.argv[1:4];metadata=harness=='metadata'
flag=pathlib.Path('/private/tmp/claude-501/-Users-dominic-ZK/4dec4925-8c43-447e-9333-6147c1c7863b/scratchpad/pv-host-restored.flag')
if not flag.is_file():
 print('HOST REBUILD GATE CLOSED: no host access or Kani; zero charge')
 sys.exit(78)
print('Host restoration instructions: '+flag.read_text(),flush=True)
now=datetime.datetime.now(datetime.timezone.utc)
assert not (datetime.datetime(2026,10,26,17,45,tzinfo=datetime.timezone.utc)<=now<datetime.datetime(2026,10,26,18,15,tzinfo=datetime.timezone.utc))
for receipt in e.glob('reservation-*.json'):
 try:
  prior=json.loads(receipt.read_text())
  if prior.get('allowed') is not False or not prior.get('utc'):continue
  elapsed=(now-datetime.datetime.fromisoformat(prior['utc'].replace('Z','+00:00'))).total_seconds()
  if elapsed<180:
   hold=dict(charged=False,reason='mandatory three-minute reservation wait',prior=str(receipt),remaining_seconds=180-elapsed,utc=now.isoformat())
   (e/f'local-reservation-hold-{name}.json').write_text(json.dumps(hold)+'\n')
   print(json.dumps(hold));sys.exit(78)
 except (ValueError,KeyError):continue
def ssh(cmd):return subprocess.run(['ssh',host,cmd],capture_output=True,text=True)
g=ssh(f'python3 /home/dombarker/project-offloads/codex-pv-runjoin-20261026/reservation-existing.py {job}/reservation-{name}.json > {job}/reservation-{name}.log 2>&1; cat {job}/reservation-{name}.log; python3 -c '+shlex.quote(f'import json;raise SystemExit(0 if json.load(open("{job}/reservation-{name}.json"))["allowed"] else 78)'))
(e/f'reservation-{name}.log').write_text(g.stdout+g.stderr)
subprocess.run(['scp','-q',f'{host}:{job}/reservation-{name}.json',str(e)],check=True)
if g.returncode:print(g.stdout+g.stderr);sys.exit(g.returncode)
# Own cache only; harness source changes are cfg(kani)-only.
for p in ['tools/r1-builder-reference/pv_srcid3.rs','tools/r1-builder-reference/records.rs','tools/r1-builder-reference/poseidon.rs','tools/r1-builder-reference/empty_roots.rs']:
 subprocess.run(['scp','-q',str(root/p),f'{host}:{job}/repo/{p}'],check=True)
rev=subprocess.check_output(['git','rev-parse','HEAD'],text=True,cwd=root).strip()
r=ssh(f'printf %s {shlex.quote(rev)} > {job}/srcid3-revision.txt');assert r.returncode==0
expected='Proof metadata compilation only' if metadata else 'Optimized proof compilation (own cache reused if present), then bounded unstubbed CBMC for '+harness
cmd=['systemd-run','--user','--scope','--quiet','--unit=pv-'+name,'-p','MemoryHigh=6G','-p','MemoryMax=8G','-p','MemorySwapMax=0','-p','TasksMax=64','env','PATH=/home/dombarker/.cargo/bin:/usr/bin:/bin','CARGO_TARGET_DIR='+job+'/kani-target','CARGO_BUILD_JOBS=4','RUSTFLAGS=-C opt-level=3 -Z mir-opt-level=4 -Z inline-mir=yes -C link-arg=-Wl,--threads=4','PV_SRCID3_EXPECTED='+expected,'python3',job+'/srcid3-receipt-run.py',name,'timeout',seconds,'cargo','kani','--no-assertion-reach-checks','-Z','stubbing','-Z','function-contracts','-Z','unstable-options','-p','aspis-statement','--lib']
if metadata:cmd+=['--only-codegen','--harness','pv_srcid3']
else:cmd+=['-j','4','--exact','--harness',harness,'--output-format','terse','--cbmc-args','--unwinding-assertions','--slice-formula']
f=e/'resume5-kani-invocations.jsonl';number=(len(f.read_text().splitlines()) if f.exists() else 0)+1
assert number<=6
record=dict(number=number,name=name,harness=harness,command=cmd,source_revision=rev)
with f.open('a') as out:out.write(json.dumps(record)+'\n')
print('CHARGED '+json.dumps(record),flush=True)
r=ssh(shlex.join(cmd));print(r.stdout+r.stderr,flush=True)
subprocess.run(['scp','-qr',f'{host}:{job}/{name}',str(e)],check=True)
s=ssh(f'systemctl --user show pv-{name}.scope -p ActiveState -p SubState')
for _ in range(10):
 if 'ActiveState=inactive' in s.stdout:break
 time.sleep(0.5)
 s=ssh(f'systemctl --user show pv-{name}.scope -p ActiveState -p SubState')
if 'ActiveState=inactive' not in s.stdout:
 ssh(f'systemctl --user stop pv-{name}.scope')
 s=ssh(f'systemctl --user show pv-{name}.scope -p ActiveState -p SubState')
(e/f'{name}-scope-ended.log').write_text(s.stdout+s.stderr)
assert 'ActiveState=inactive' in s.stdout,s.stdout
sys.exit(r.returncode)
