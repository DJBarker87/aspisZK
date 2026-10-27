from pathlib import Path
import json,re,hashlib,subprocess
root=Path(__file__).resolve().parents[2];ev=root/'evidence/pv-cblib-20261027';t=json.loads((ev/'TALLY-resume9.json').read_text())
assert len(t['used_ids'])==len(set(t['used_ids']))
assert all(52400<=i<=52699 for i in t['used_ids'])
rows=[json.loads((ev/f'{i}.json').read_text()) for i in t['lean_charged']]
accepted=[r for r in rows if r['exit']==0];rejected=[r for r in rows if r['exit']!=0]
for r in accepted:
 for line in r['axioms']:
  for group in re.findall(r'\[([^]]*)\]',line):
   assert set(x.strip() for x in group.split(',') if x.strip())<= {'propext','Classical.choice','Quot.sound'},(r['attempt'],line)
latest={r['module']:r for r in accepted}
current={}
for name,r in latest.items():
 p=root/'docs/research/v8-r0-zk-20261009/lean'/f'{name}.lean'
 current[name]={'accepted_attempt':r['attempt'],'source_sha256':r['source_sha256'],'current_source_matches':p.exists() and hashlib.sha256(p.read_bytes()).hexdigest()==r['source_sha256']}
report={'base':'4aaa5ae9a2','revision':subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip(),'tally':t,'charged':len(rows),'accepted':len(accepted),'rejected':len(rejected),'uncharged_ids':sorted(set(t['used_ids'])-set(t['lean_charged'])),'peak_accepted_rss_kib':max(int(r['peak_rss_kib'] or 0) for r in accepted),'accepted_swaps':sorted(set(r['swap'] for r in accepted)),'all_accepted_axioms_standard':True,'accepted_modules':current,'receipts':[{k:r[k] for k in ['attempt','module','exit','wall','peak_rss_kib','swap','source_revision','source_sha256','axioms']} for r in rows]}
(ev/'RESUME9-RECEIPTS.json').write_text(json.dumps(report,indent=2)+'\n')
print({k:report[k] for k in ['charged','accepted','rejected','uncharged_ids','peak_accepted_rss_kib','accepted_swaps']})
