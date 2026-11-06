from pathlib import Path
import hashlib,json,difflib
B=Path(__file__).resolve().parent;S=B/'NLC_src';pins=json.loads((B/'NLC_SOURCE_PINS.json').read_text());sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
n='crates/aspis-r1-cost-probe/src/NLC_native.rs';p=S/n;assert sha(p)==pins[n]
original=p.read_text();assert 'check_construct_window' not in original
p.write_text(original+'\n'+(B/'NLC_fields.rs.txt').read_text());pins[n]=sha(p)
patch=''
for parent,module in [('r1_semantic.rs','NLC_native'),('r1_wire.rs','NLC_factory')]:
 n='crates/aspis-r1-cost-probe/src/'+parent;p=S/n;raw=p.read_text();suffix='\n#[cfg(kani)]\n#[path = "'+module+'.rs"]\npub(crate) mod '+module+';\n';assert raw.endswith(suffix);base=raw[:-len(suffix)]
 patch+=''.join(difflib.unified_diff(base.splitlines(True),raw.splitlines(True),fromfile='a/'+n,tofile='b/'+n))
 q=p.with_name(module+'.rs');patch+='--- /dev/null\n+++ b/'+str(q.relative_to(S))+'\n@@ -0,0 +1,'+str(len(q.read_text().splitlines()))+' @@\n'+''.join('+'+s+'\n' for s in q.read_text().splitlines())
(B/'NLC_NATIVE.patch').write_text(patch);(B/'NLC_SOURCE_PINS.json').write_text(json.dumps(pins,indent=2))
print('Installed eight distinct field properties; source constructor and retired shape unchanged')
