from pathlib import Path
import json,hashlib,difflib
B=Path(__file__).resolve().parent;S=B/'NLZ_src';sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
p=S/'crates/aspis-r1-cost-probe/src/NLZ_native.rs';p.write_text((B/'NLZ_native.rs.txt').read_text())
x=json.loads((B/'NLZ_SOURCE_PINS.json').read_text());x[str(p.relative_to(S))]=sha(p);(B/'NLZ_SOURCE_PINS.json').write_text(json.dumps(x,indent=2))
patch=''
for parent,mod in [('r1_semantic.rs','NLZ_native'),('r1_wire.rs','NLZ_factory')]:
 n='crates/aspis-r1-cost-probe/src/'+parent;a=(B/'NLZ_frozen'/n).read_text();b=(S/n).read_text();patch+=''.join(difflib.unified_diff(a.splitlines(True),b.splitlines(True),fromfile='a/'+n,tofile='b/'+n));q=S/n;q=q.with_name(mod+'.rs');patch+='--- /dev/null\n+++ b/'+str(q.relative_to(S))+'\n@@ -0,0 +1,'+str(len(q.read_text().splitlines()))+' @@\n'+''.join('+'+l+'\n' for l in q.read_text().splitlines())
(B/'NLZ_NATIVE.patch').write_text(patch)
print('Own harness updated and strict source pins/patch refreshed; frozen bodies unchanged')
