from pathlib import Path
import json,hashlib,difflib
B=Path(__file__).resolve().parent;S=B/'NKQ_src';pins=json.loads((B/'NKQ_SOURCE_PINS.json').read_text());frozen=json.loads((B/'NKQ_FROZEN_FILE_PINS.json').read_text())
n='crates/aspis-r1-cost-probe/src/r1_semantic.rs';p=S/n;old=p.read_text();assert hashlib.sha256(p.read_bytes()).hexdigest()==frozen[n]
p.write_text(old+'\n#[cfg(kani)]\nmod NKQ_rejections;\n');q=p.with_name('NKQ_rejections.rs');q.write_text((B/'NKQ_rejections.rs.txt').read_text())
pins[n]=hashlib.sha256(p.read_bytes()).hexdigest();pins[str(q.relative_to(S))]=hashlib.sha256(q.read_bytes()).hexdigest();del frozen[n]
(B/'NKQ_SOURCE_PINS.json').write_text(json.dumps(pins,indent=2));(B/'NKQ_FROZEN_FILE_PINS.json').write_text(json.dumps(frozen,indent=2))
patch=''.join(difflib.unified_diff(old.splitlines(True),p.read_text().splitlines(True),fromfile='a/'+n,tofile='b/'+n))+'\n'.join(['--- /dev/null','+++ b/'+str(q.relative_to(S)),'@@ -0,0 +1,'+str(len(q.read_text().splitlines()))+' @@'])+'\n'+''.join('+'+s+'\n' for s in q.read_text().splitlines())
(B/'NKQ_NATIVE.patch').write_text(patch);print('NKQ cfg-only rejection harness installed in frozen scratch')
