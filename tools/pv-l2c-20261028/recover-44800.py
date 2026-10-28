from pathlib import Path
import json,subprocess,hashlib,re,datetime,sys
R=Path.cwd(); E=R/'evidence/pv-l2c-20261028/resume-d355'; H='/home/dombarker/project-offloads/codex-pv-l2c-20261028'
D=E/'batch-44800';spec=json.loads((D/'manifest.json').read_text());gate=json.loads((D/'reservation.json').read_text());cmd=json.loads((D/'command.json').read_text())
def ssh(c):return subprocess.run(['ssh','dombarker@100.108.41.90',c],capture_output=True,text=True)
# Recover exactly the invocations actually launched; never re-submit after SSH loss.
for x in spec:
 a=x['attempt'];q=ssh(f'cat {H}/evidence/done-{a}.json')
 if q.returncode:break
 x.update(json.loads(q.stdout));x['reservation']=gate;x['scope_command']=cmd
 for label in ['out','time','deps']:
  suffix='json' if label=='deps' else 'log';q=ssh(f'cat {H}/evidence/{label}-{a}.{suffix}');assert q.returncode==0,q.stderr;(E/f'{label}-{a}.{suffix}').write_text(q.stdout)
 out=(E/f'out-{a}.log').read_text();tim=(E/f'time-{a}.log').read_text();x['dependencies']=json.loads((E/f'deps-{a}.json').read_text());x['deps_fingerprint']=hashlib.sha256((E/f'deps-{a}.json').read_bytes()).hexdigest();x['axioms']=re.findall(r"'[^']+' (?:depends on axioms: \[[\s\S]*?\]|does not depend on any axioms)",out)
 for key,pat in [('peak_rss_bytes',r'Maximum resident set size \(kbytes\): (\d+)'),('swaps',r'Swaps: (\d+)'),('host_wall',r'Elapsed \(wall clock\) time.*: (.+)')]:
  v=re.search(pat,tim);x[key]=(int(v[1])*1024 if key=='peak_rss_bytes' else v[1]) if v else None
 x['accepted']=x['exit']==0 and 'sorryAx' not in out and 'error:' not in out
 (E/f'used-{a}.json').write_text(json.dumps(dict(attempt=a,target=x['module'],utc=datetime.datetime.now(datetime.timezone.utc).isoformat()))+'\n')
 (E/f'{a}-{x["module"].replace(".","_")}.lean.txt').write_text(x.pop('source'))
 (E/f'receipt-{a}.json').write_text(json.dumps(x,indent=2)+'\n');print('RECEIPT',a,x['exit'],x['host_wall'],x['peak_rss_bytes'],flush=True)
 if not x['accepted']:print(out[-5000:]);sys.exit(1)
