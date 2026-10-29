from pathlib import Path
import subprocess,json,shlex,time,sys,re
E=Path('evidence/pv-rj4idb-20261029');H='/home/dombarker/project-offloads/codex-pv-rj4idb-20261029';host='dombarker@100.108.41.90';suite=sys.argv[1];assert suite in ['powers','statement'];tag='native-'+suite
assert not (E/(tag+'-receipt.json')).exists()
for f in E.glob('refusal-*.json'):
 assert time.time()>=json.loads(f.read_text())['epoch']+180,'cooldown'
cmd=['systemd-run','--user','--scope','--quiet','--unit=rj4idb-'+tag,'-p','MemoryHigh=6G','-p','MemoryMax=8G','-p','MemorySwapMax=0','-p','TasksMax=64','/usr/bin/time','-v','-o',H+'/evidence/'+tag+'-time.log','python3',H+'/native-host.py',suite]
remote='bash -o pipefail -c '+shlex.quote('python3 /home/dombarker/project-offloads/codex-pv-runjoin-20261026/reservation-existing.py '+H+'/evidence/'+tag+'-admission.json > '+H+'/evidence/'+tag+'-admission.log 2>&1 && python3 -c '+shlex.quote('import json;assert json.load(open('+repr(H+'/evidence/'+tag+'-admission.json')+'))["allowed"] is True')+' && '+shlex.join(cmd))
(E/(tag+'-submission.json')).write_text(json.dumps(dict(command=cmd,expected_phase='optimized compilation, then '+suite+' finite differential; no extraction',source_revision=subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip()),indent=2))
x=subprocess.run(['ssh',host,remote],capture_output=True,text=True);(E/(tag+'-output.log')).write_text(x.stdout+x.stderr)
for suffix in ['admission.json','admission.log','time.log','result.json','compile.log']:
 r=subprocess.run(['scp','-q',host+':'+H+'/evidence/'+tag+'-'+suffix,str(E/(tag+'-'+suffix))],capture_output=True,text=True)
 if r.returncode and suffix in ['admission.json','time.log']:raise RuntimeError(r.stderr)
ad=json.loads((E/(tag+'-admission.json')).read_text())
if x.returncode==78 or not ad.get('allowed'):
 (E/('refusal-'+tag+'.json')).write_text(json.dumps(dict(ad,epoch=time.time())));print('REFUSED',x.returncode,ad.get('reason'));sys.exit(78)
t=(E/(tag+'-time.log')).read_text();v=lambda pat:re.search(pat,t)[1]
receipt=dict(target=cmd,exit=x.returncode,wall=v(r'Elapsed \(wall clock\) time \(h:mm:ss or m:ss\): ([0-9:.]+)'),peak_rss_bytes=int(v(r'Maximum resident set size \(kbytes\): (\d+)'))*1024,swaps=int(v(r'Swaps: (\d+)')),source_revision=json.loads((E/(tag+'-submission.json')).read_text())['source_revision'],axioms='N/A native finite validation',admission=ad,accepted=x.returncode==0)
(E/(tag+'-receipt.json')).write_text(json.dumps(receipt,indent=2)+'\n');print(json.dumps({k:v for k,v in receipt.items() if k not in ['admission','target']}));print(x.stdout+x.stderr);sys.exit(x.returncode)
