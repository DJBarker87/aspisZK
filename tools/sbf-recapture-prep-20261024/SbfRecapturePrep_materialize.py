#!/usr/bin/env python3
"""Stream only validated frozen Git blobs into exclusively created own files."""
import base64,hashlib,json,os,pathlib,re,resource,shlex,subprocess,sys,time
T=pathlib.Path(__file__).resolve().parent;E=T.parents[1]/'evidence/sbf-recapture-prep-20261024'
BASE='009b61e61bf52dba92c4fbefae79702a938f05b3';REV='4bb3b3f51e16b4525f1d10336e2b0bcbbd775387'
STAGE='/home/dombarker/project-offloads/codex-cx-sbf-recapture-20261024'
S10='docs/research/100bit-spend-path-20261013/evidence/s10-repin3-20261023/'
def show(p):return subprocess.check_output(['git','show',BASE+':'+p])
def sha(b):return hashlib.sha256(b).hexdigest()
start=time.monotonic();pins={}
manifest=show(S10+'source-inputs.json');assert sha(manifest)=='a84a528cfc4b294c603fe5381343cdaf9df0547467bcc94e61a67e5111adb9d1'
x=json.loads(manifest);assert x['source_revision']==REV and len(x['files'])==7978 and not x['additional_workspace_inputs']
exclusions=show(S10+'snapshot-exclusions.json');json.loads(exclusions) # policy read before source blobs
names=[r['path'] for r in x['files']];assert len(set(names))==7978
blocked=[];classifications=[]
for name in names:
 p=pathlib.PurePosixPath(name)
 assert not p.is_absolute() and '..' not in p.parts and str(p)==name
 if re.search(r'(keypair|wallet|secret|credential|seed|mnemonic|\.pem$|\.key$|\.env(?:\.|$)|id_rsa)',name,re.I):
  # These suffixes are textual source/config/docs, not wallet key material.
  if p.suffix in ('.rs','.toml','.md','.lock'):classifications.append(dict(path=name,classification='source/config/document name; no key material file'))
  else:blocked.append(name)
assert not blocked,('unauthorized possible key inputs; do not read',blocked)
tree={}
for line in subprocess.check_output(['git','ls-tree','-rz',REV]).split(b'\0'):
 if not line:continue
 header,name=line.split(b'\t',1);mode,kind,oid=header.decode().split();tree[name.decode()]=(mode,kind,oid)
for name in names:
 mode,kind,oid=tree[name];assert kind=='blob' and mode in ('100644','100755'),(name,mode,kind)
# Receiver does not extract archives, follow links, or accept extra destinations.
receiver=r'''
import sys,json,base64,pathlib,os,hashlib,resource,time
resource.setrlimit(resource.RLIMIT_AS,(512*1024**2,512*1024**2))
s=time.monotonic();root=pathlib.Path('/home/dombarker/project-offloads/codex-cx-sbf-recapture-20261024')
assert root.stat().st_uid==os.getuid() and not root.is_symlink() and (root/'OWNER').read_text()=='SbfRecapturePrep 20261024\n'
assert not (root/'src').exists()
rows=[]
for line in sys.stdin.buffer:
 r=json.loads(line);rel=pathlib.PurePosixPath(r['path']);assert not rel.is_absolute() and '..' not in rel.parts
 p=root/rel
 for parent in p.parents:
  if parent==root:break
  assert not parent.is_symlink()
 p.parent.mkdir(parents=True,exist_ok=True)
 b=base64.b64decode(r['data'],validate=True);assert len(b)==r['bytes'] and hashlib.sha256(b).hexdigest()==r['sha256']
 with p.open('xb') as f:f.write(b)
 os.chmod(p,r['mode']);assert p.stat().st_size==r['bytes'] and hashlib.sha256(p.read_bytes()).hexdigest()==r['sha256']
 rows.append({k:v for k,v in r.items() if k!='data'})
expected={r['path'] for r in rows if r['path'].startswith('src/')}
actual={'src/'+str(p.relative_to(root/'src')) for p in (root/'src').rglob('*') if p.is_file()}
assert expected==actual
raw=root/'materialized-files.json';raw.write_text(json.dumps(rows,indent=2)+'\n')
u=resource.getrusage(0)
print(json.dumps(dict(source_files=len(expected),files=len(rows),bytes=sum(r['bytes'] for r in rows),entire_materialization_verified=True,raw_manifest_sha256=hashlib.sha256(raw.read_bytes()).hexdigest(),raw_manifest_bytes=raw.stat().st_size,wall_seconds=time.monotonic()-s,peak_rss_kib=u.ru_maxrss,swaps=u.ru_nswap,print_axioms='N/A')))
'''
cmd=['ssh','-o','BatchMode=yes','-o','ConnectTimeout=15','dombarker@100.108.41.90','python3 -c '+shlex.quote(receiver)]
p=subprocess.Popen(cmd,stdin=subprocess.PIPE,stdout=subprocess.PIPE,stderr=subprocess.PIPE)
# git cat-file reads only the vetted object IDs (never live checkout files).
git=subprocess.Popen(['git','cat-file','--batch'],stdin=subprocess.PIPE,stdout=subprocess.PIPE)
def send(name,b,mode,oid=None):
 row=dict(path=name,bytes=len(b),sha256=sha(b),mode=mode,git_blob=oid)
 p.stdin.write(json.dumps(dict(row,data=base64.b64encode(b).decode())).encode()+b'\n')
for r in x['files']:
 mode,kind,oid=tree[r['path']];git.stdin.write((oid+'\n').encode());git.stdin.flush()
 header=git.stdout.readline().decode().split();assert header[:2]==[oid,'blob'];size=int(header[2]);b=git.stdout.read(size);assert git.stdout.read(1)==b'\n'
 assert len(b)==r['bytes'] and sha(b)==r['sha256'],r['path']
 send('src/'+r['path'],b,int(mode,8)&0o777,oid)
git.stdin.close();assert git.wait()==0
wrapper=show('tools/s10-repin3-20261023/rustc-diagnostics.py');assert sha(wrapper)=='fa74d69e097b6eab43809943614133081abb6beb19406018961402b86494ff84'
extras={'rustc-diagnostics.py':wrapper,'source-inputs.json':manifest,'snapshot-exclusions.json':exclusions,'platform-release.txt':show('evidence/sbf-identity-20261024/platform-release.txt')}
for name,b in extras.items():send(name,b,0o755 if name.endswith('.py') else 0o600);pins[name]=dict(sha256=sha(b),bytes=len(b))
p.stdin.close();out=p.stdout.read();err=p.stderr.read();exit=p.wait()
(E/'materialize.stdout.json').write_bytes(out);(E/'materialize.stderr.txt').write_bytes(err)
u=resource.getrusage(0);c=resource.getrusage(resource.RUSAGE_CHILDREN)
r=dict(command=cmd,exit=exit,wall_seconds=time.monotonic()-start,peak_rss_bytes=u.ru_maxrss,children_peak_rss_bytes=c.ru_maxrss,swaps=u.ru_nswap+c.ru_nswap,source_revision=REV,job_revision=subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip(),script_sha256=sha(pathlib.Path(__file__).read_bytes()),inputs=pins,manifest_sha256=sha(manifest),key_name_classification=classifications,blocked=blocked,print_axioms='N/A')
(E/'materialize.transport.json').write_text(json.dumps(r,indent=2)+'\n');print(out.decode());print(err.decode(),file=sys.stderr);sys.exit(exit)
