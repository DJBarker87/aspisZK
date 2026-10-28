from pathlib import Path
import json,subprocess,sys
R=Path(__file__).resolve().parents[2];E=R/'evidence/pv-l1-20261028';a=int(sys.argv[1]);accepted={r['target'].replace('/','.') for p in E.glob('receipt-*.json') if (r:=json.loads(p.read_text())).get('accepted')};by={r['module']:r for r in json.loads((E/'source-frontier.json').read_text())}
for k in list(range(8,21))+[26]:
 m=f'PV_L1_Source_{k:03}'
 if m in accepted:continue
 if a>=51697:break
 missing=[d for d in by[m]['dependencies'] if d not in accepted];assert not missing,(m,missing)
 p=subprocess.run([sys.executable,str(R/'tools/pv-l1-20261028/check.py'),str(a),m],capture_output=True,text=True)
 print(p.stdout[-3000:] if p.returncode else p.stdout[-500:],flush=True)
 if p.returncode:sys.exit(p.returncode)
 accepted.add(m);a+=1
