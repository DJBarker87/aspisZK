import hashlib,json,pathlib,resource,shlex,subprocess,time
B=pathlib.Path('evidence/sbf-resolve-20261025');src=pathlib.Path('tools/sbf-resolve-20261025/SbfResolve_export.py').read_text();files=[]
for q in [1,2]:
 j=json.loads((B/f'SbfResolve-query-{q}.stdout').read_text())
 for k in ['stdout','trace']:
  r=j['outputs'][k];files.append(dict(name=f'query-{q}.{k}',bytes=r['bytes'],sha256=r['sha256']))
queries=json.loads((B/'SbfResolve-query-2.stdout').read_text())['compiler_queries'];raw=(''.join(json.dumps(x)+'\n' for x in queries)).encode()
files.append(dict(name='compiler-queries.jsonl',bytes=len(raw),sha256=hashlib.sha256(raw).hexdigest()))
req=json.dumps(dict(files=files))+'\n';cmd=['/usr/bin/python3','-I','-S','-B','-c',src];argv=['ssh','-o','BatchMode=yes','-o','ConnectTimeout=10','dombarker@100.108.41.90',' '.join(map(shlex.quote,cmd))]
t=time.monotonic();p=subprocess.run(argv,input=req.encode(),stdout=subprocess.PIPE,stderr=subprocess.PIPE,timeout=30)
assert p.returncode==0,p.stderr.decode();data=p.stdout;records=[]
while data:
 header,data=data.split(b'\n',1);r=json.loads(header);body,data=data[:r['bytes']],data[r['bytes']:];assert len(body)==r['bytes'] and hashlib.sha256(body).hexdigest()==r['sha256'];dest=B/('SbfResolve-raw-'+r['name']);dest.write_bytes(body);records.append(r)
u=resource.getrusage(0);receipt=dict(command=argv,request=req,source_revision=subprocess.check_output(['git','rev-parse','HEAD']).decode().strip(),helper_sha256=hashlib.sha256(src.encode()).hexdigest(),exit=p.returncode,wall_seconds=time.monotonic()-t,peak_rss_bytes=u.ru_maxrss,swap=u.ru_nswap,stderr=p.stderr.decode(),files=records,print_axioms='N/A')
(B/'SbfResolve-export-transport.json').write_text(json.dumps(receipt,indent=2)+'\n');print(json.dumps(records,indent=2))
