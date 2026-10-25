"""Read only the finished own metadata artifacts; never repeat queries."""
import hashlib,json,os,pathlib,resource,sys,time
P=pathlib.Path;O=P('/home/dombarker/project-offloads/codex-cx-sbf-recapture-20261024/SbfResolve-20261025-v1')
def main():
 req=json.loads(sys.stdin.readline());t=time.monotonic();assert os.getuid()==1000 and O.stat().st_uid==1000 and not O.is_symlink()
 for row in req['files']:
  name=row['name'];assert '/' not in name and name in ['query-1.stdout','query-2.stdout','query-1.trace','query-2.trace','compiler-queries.jsonl']
  p=O/name;assert p.is_file() and not p.is_symlink() and p.stat().st_nlink==1 and p.stat().st_size<5_000_000
  b=p.read_bytes();assert len(b)==row['bytes'] and hashlib.sha256(b).hexdigest()==row['sha256']
  header=json.dumps(dict(name=name,bytes=len(b),sha256=hashlib.sha256(b).hexdigest()))+'\n';sys.stdout.buffer.write(header.encode()+b);sys.stdout.buffer.flush()
 # Oversized derived manifest remains remote: stream summary, no whole JSON copy.
 mf=O/'private-cache-complete.jsonl';h=hashlib.sha256();files=total=0;packages=set();indices=set();markers=0
 with mf.open('rb') as f:
  for line in f:
   h.update(line);r=json.loads(line);files+=1;total+=r['bytes'];rel=P(r['path']).relative_to(O/'cargo/registry')
   if rel.parts[0]=='src':packages.add(rel.parts[2]);markers+=rel.name=='.cargo-ok'
   if rel.parts[0]=='index' and '.cache' in rel.parts:indices.add(str(rel))
 target=[]
 for p in (O/'target').rglob('*'):
  assert not p.is_symlink();target.append(dict(path=str(p.relative_to(O)),bytes=p.stat().st_size,type='file' if p.is_file() else 'directory'))
 u=resource.getrusage(0);data=dict(exit=0,wall_seconds=time.monotonic()-t,peak_rss_kib=u.ru_maxrss,swap=u.ru_nswap,print_axioms='N/A',remote_manifest=dict(path=str(mf),bytes=mf.stat().st_size,sha256=h.hexdigest(),regular_files=files,file_bytes=total,packages=len(packages),index_files=len(indices),completion_markers=markers,marker_kind='official Cargo LockMetadata v1 completion only, not checksum/fingerprint forgery'),target_entries=target)
 b=json.dumps(data,sort_keys=True).encode();sys.stdout.buffer.write((json.dumps(dict(name='export-summary.json',bytes=len(b),sha256=hashlib.sha256(b).hexdigest()))+'\n').encode()+b)
if __name__=='__main__':main()
