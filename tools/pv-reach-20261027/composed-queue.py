import subprocess,sys,json,pathlib
R=pathlib.Path(__file__).resolve().parents[2];E=R/'evidence/pv-reach-20261027/resume4'
first,last=map(int,sys.argv[1:])
for i in range(first,last+1):
 a=37322+i
 r=subprocess.run([sys.executable,str(R/'tools/pv-reach-20261027/resume4-check.py'),str(a),f'R1Z/PV_RE_ComposedChunk{i:03}'],capture_output=True,text=True)
 p=E/f'receipt-{a}.json'
 if p.exists():
  d=json.loads(p.read_text());print(json.dumps({k:d.get(k) for k in ['attempt','target','exit','wall_seconds','peak_rss_bytes','accepted']}),flush=True)
  if not d['accepted']:print(r.stdout[-2500:]+r.stderr[-500:],flush=True)
  if d['exit'] is None:sys.exit(2)
 else:
  print(r.stdout+r.stderr,flush=True);sys.exit(r.returncode or 2)
