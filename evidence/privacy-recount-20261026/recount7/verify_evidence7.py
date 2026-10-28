from auditlib7 import *
checks=[]
# Recorded complete-body bindings remain tied to the pinned candidate sources.
for x in list(manifest):
 if x['ref']!='rw' or not x['path'].endswith('.json') or not any(t in x['path'] for t in ['-binding.json','STRUCTURAL','d336-native-reuse']):continue
 d=json.loads(read('rw',x['path']))
 def walk(v):
  if isinstance(v,dict):
   files=v.get('files')
   if isinstance(files,dict):
    for path,h in files.items():
     if isinstance(h,str) and re.fullmatch('[a-f0-9]{64}',h):check(path,h)
   path=v.get('path');h=v.get('sha256',v.get('source_sha256'))
   if path and isinstance(h,str) and re.fullmatch('[a-f0-9]{64}',h):check(path,h)
   for a in v.values():walk(a)
  elif isinstance(v,list):
   for a in v:walk(a)
 def check(path,h):
  s=read('rw',path)
  checks.append(dict(binding=x['path'],path=path,expected=h,actual=hashlib.sha256(s.encode()).hexdigest() if s is not None else None,matches=s is not None and hashlib.sha256(s.encode()).hexdigest()==h))
 walk(d)
# Every full receipt's release-required fields and axiom whitelist, independently parsed.
rs=json.loads((P/'reused-receipts7.json').read_text());result=[]
for a in rs:
 v=a['receipt'];axioms=v.get('axioms',v.get('print_axioms',v.get('axiom_output',[])))
 bad=[]
 axtext='\n'.join(axioms)
 path=a['path']
 if 'batch2' in path:
  axtext=read(a['ref'],path[:-5]+'-stdout.log');read(a['ref'],path[:-5]+'-time.log')
 elif 'batch3' in path:axtext=read(a['ref'],path.rsplit('/',1)[0]+'/stdout.log')
 elif 'relink' in path:axtext=read(a['ref'],path.rsplit('/',1)[0]+'/output.log')
 elif 'runjoin' in path:axtext=read(a['ref'],path.replace('receipt-','out-').replace('.json','.log'))
 assert axtext

 for z in re.finditer(r'depends on axioms:\s*\[([^]]*)\]',axtext,re.S):
  bad += [n.strip() for n in z[1].split(',') if n.strip() not in ['propext','Classical.choice','Quot.sound']]
 assert 'sorryAx' not in axtext
 assert not bad,(a['path'],bad)
 target=v.get('module',v.get('target'));exit=v.get('exit',v.get('exit_status'));wall=v.get('wall',v.get('wall_seconds'));rss=v.get('peak_rss_kib',v.get('peak_rss_bytes'));sw=v.get('swap',v.get('swaps'));rev=v.get('source_revision')
 assert exit==0 and target and wall is not None and rss and str(sw)=='0' and rev and axioms,a['path']
 result.append(dict(ref=a['ref'],path=a['path'],target=target,exit=exit,wall=wall,peak_rss=rss,rss_unit='bytes' if 'peak_rss_bytes' in v else 'KiB',swap=sw,source_revision=rev,axiom_reports=len(re.findall(r"depends on axioms:|does not depend on any axioms",axtext)),axioms_standard=True))
(P/'receipt-audit7.json').write_text(json.dumps(result,indent=2)+'\n')
(P/'native-pin-checks7.json').write_text(json.dumps(checks,indent=2)+'\n')
patch=read('research','evidence/kani-mitig-20261028/KMX_copy_stubs.patch');assert hashlib.sha256(patch.encode()).hexdigest()=='bcdf749b78eb6143789500d98d64ec3d407b8a17a6d1290c70c822473e8e9a67'
(P/'manifest.json').write_text(json.dumps(manifest,indent=2)+'\n')
print('receipts',len(result),'source hash checks',len(checks),'mismatches',[x for x in checks if not x['matches']])
