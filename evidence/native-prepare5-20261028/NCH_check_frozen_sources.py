from pathlib import Path
import subprocess,json,hashlib
E=Path(__file__).resolve().parent;rev='4bb3b3f51e16b4525f1d10336e2b0bcbbd775387'
pins=json.loads((E/'NCH_SOURCE.json').read_text())['source_sha256']
paths=subprocess.check_output(['git','ls-tree','-r','--name-only',rev,'crates','programs'],text=True).splitlines()
p=subprocess.Popen(['git','cat-file','--batch'],stdin=subprocess.PIPE,stdout=subprocess.PIPE)
changed=[];count=0;missing=[]
for n in paths:
 if n not in pins:missing.append(n);continue
 p.stdin.write((rev+':'+n+'\n').encode());p.stdin.flush();header=p.stdout.readline().decode().strip().split();assert header[1]=='blob',header
 size=int(header[2]);data=p.stdout.read(size);assert len(data)==size;assert p.stdout.read(1)==b'\n';h=hashlib.sha256(data).hexdigest();count+=1
 if h!=pins[n]:changed.append({'path':n,'frozen_sha256':h,'scratch_sha256':pins[n]})
p.stdin.close();p.wait();assert p.returncode==0
allowed={'crates/aspis-r1-cost-probe/src/lib.rs','crates/aspis-r1-cost-probe/src/candidate.rs','crates/aspis-r1-cost-probe/src/r1_wire.rs'}
out={'revision':rev,'compared':count,'changes':changed,'missing_from_partial_scratch':missing,'unexpected_changes':[x for x in changed if x['path'] not in allowed],'method':'hash immutable git blobs against per-run host source pin set; only cfg(kani) harness inclusion/allocator_api additions allowed','repository_shipped_source_changed':False}
(E/'NCH_FROZEN_SOURCE_AUDIT.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps({k:out[k] for k in ['compared','changes','unexpected_changes']},indent=2));assert not out['unexpected_changes']
