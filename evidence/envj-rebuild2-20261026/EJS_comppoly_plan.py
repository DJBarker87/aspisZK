"""Plan only needed ancestors from the historically pinned package revision."""
from pathlib import Path
import json,base64,re,hashlib,subprocess,shlex
O=Path(__file__).parent;pkg=json.load(open(O/'EJS_comppoly-pinned-sources.json'));blocked=json.load(open(O/'EJS_recursive-frontier.json'))['blocked'];roots=[m for m in blocked if m.startswith('CompPoly/')]
remote='''from pathlib import Path
import json
T=Path('/home/dombarker/project-offloads/aspis-fs-generic-20261006/evidence');rs=json.loads((T/'EJR_all-restored-sources.json').read_text())
for p in T.glob('EJS_*-sources.json'):rs.extend(json.loads(p.read_text()))
print(json.dumps({r['module']:r['source_sha256'] for r in rs}))
'''
known=json.loads(subprocess.check_output(['ssh','dombarker@100.108.41.90','python3 -c '+shlex.quote(remote)],text=True));queue=list(roots);needed={};absent=[]
while queue:
 m=queue.pop()
 if m in needed:continue
 if m not in pkg['sources']:absent.append(m);continue
 r=pkg['sources'][m];b=base64.b64decode(r['source_base64']);assert hashlib.sha256(b).hexdigest()==r['source_sha256']
 if m in known:
  assert known[m]==r['source_sha256'],('known source pin differs from historically recorded package',m)
  continue
 s=re.sub(r'/\-.*?\-/','',b.decode(),flags=re.S);s=re.sub(r'--[^\n]*','',s)
 ds=[v.replace('.','/') for ln in s.splitlines() if re.match(r'^\s*(?:public\s+|private\s+)?import\s',ln) for v in re.sub(r'^\s*(?:public\s+|private\s+)?import\s+(?:all\s+)?','',ln).split() if re.fullmatch(r'[\w.]+',v)]
 if re.search(r'\b(?:sorry|admit|native_decide)\b|^\s*axiom\s',s,re.M):raise RuntimeError('forbidden source token '+m)
 oid=hashlib.sha1(b'blob '+str(len(b)).encode()+b'\0'+b).hexdigest();needed[m]=dict(module=m,**r,blob=oid,bytes=len(b),imports=ds,source_repository='https://github.com/Verified-zkEVM/CompPoly',upstream_revision=pkg['revision'],attestation=dict(evidence='docs/research/100bit-spend-path-20261013/evidence/soundness-env-20261020/retained-comppoly-inventory.json',scope='immutable package revision; all 11 independently recorded source hashes match',archive_sha256=pkg['archive_sha256']));queue.extend(v for v in ds if v.startswith('CompPoly/'))
# Verify each source against this repository's historical package snapshot as well.
history=json.load(open(O/'EJS_recursive-history-resolution.json'))['found'];sample=next(iter(history.values()));rev=sample['revision'];prefix=sample['path'].split('/CompPoly/')[0]
p=subprocess.Popen(['git','cat-file','--batch-check'],stdin=subprocess.PIPE,stdout=subprocess.PIPE)
for m,r in needed.items():
 path=prefix+'/'+m+'.lean';p.stdin.write((rev+':'+path+'\n').encode());p.stdin.flush();h=p.stdout.readline().decode().split();assert len(h)==3 and h[0]==r['blob'] and h[1]=='blob',(m,h,r['blob']);r.update(revision=rev,path=path,repository_blob_verified=True)
p.terminate()
(O/'EJS_comppoly-needed-payload.json').write_text(json.dumps(dict(rows=list(needed.values())))+'\n');(O/'EJS_comppoly-plan.json').write_text(json.dumps(dict(roots=roots,modules=[{k:v for k,v in r.items() if k!='source_base64'} for r in needed.values()],absent=absent,upstream_revision=pkg['revision'],repository_snapshot_revision=rev,proof_source_edits=False),indent=2)+'\n');print('needed exact package sources',len(needed),'all repository blobs verified')
