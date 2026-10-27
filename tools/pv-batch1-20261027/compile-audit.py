from pathlib import Path
import subprocess,sys,json
E=Path('evidence/pv-batch1-20261027');P=E/'TALLY.json';H='/home/dombarker/project-offloads/codex-pv-batch1-20261027'
a=int(sys.argv[1]);module=sys.argv[2];expected=['PV_B1_AuditSource','PV_B1_AuditTyped','PV_B1_AuditManifest']
t=json.loads(P.read_text());assert module==expected[t['lean_charged']-97] and a==t['next_unused_id'] and a<53897 and a not in t['used_ids'] and 97<=t['lean_charged']<100
t['used_ids'].append(a);t['next_unused_id']=a+1;P.write_text(json.dumps(t,indent=2)+'\n')
r=subprocess.run(['ssh','dombarker@100.108.41.90',f'cd {H} && python3 lean.py {a} {module}'],capture_output=True,text=True)
(E/f'lean-{a}-launcher.log').write_text(r.stdout+r.stderr)
records=[]
for line in r.stdout.splitlines():
 try:
  x=json.loads(line)
  if isinstance(x,dict) and x.get('attempt')==a: records.append(x)
 except json.JSONDecodeError:pass
if not records:
 print(r.stdout+r.stderr,flush=True)
 raise SystemExit('No charged scope: consumed ID; wait on admission refusal, never reuse')
rec=records[-1]
if rec['charged']:t['lean_charged']+=1
t['stage']='reserved final audits';P.write_text(json.dumps(t,indent=2)+'\n');print(json.dumps(rec),flush=True)
if r.returncode:print((r.stdout+r.stderr)[-7000:],flush=True)
raise SystemExit(r.returncode)
