from pathlib import Path
import json,hashlib,difflib
B=Path.cwd();S=B/'NLI_src';P=Path('/home/dombarker/project-offloads/codex-cx-tx1-driver2-20261109/NLC_src')
H=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
pins=json.loads((B/'NLI_SOURCE_PINS.json').read_text());patch=''
for parent,module,file in [('crates/aspis-r1-cost-probe/src/r1_semantic.rs','NLI_rounds','NLI_rounds.rs.txt'),('crates/aspis-r1-cost-probe/src/r1_wire.rs','NLI_factory','NLI_factory.rs.txt'),('programs/r1-cost-probe/src/lib.rs','NLI_program','NLI_program.rs.txt')]:
 p=S/parent;q=p.with_name(module+'.rs');q.write_text((B/file).read_text());pins[str(q.relative_to(S))]=H(q)
 before=(P/parent).read_text();after=p.read_text()
 patch+=''.join(difflib.unified_diff(before.splitlines(True),after.splitlines(True),fromfile='a/'+parent,tofile='b/'+parent))
 patch+='--- /dev/null\n+++ b/'+str(q.relative_to(S))+'\n@@ -0,0 +1,'+str(len(q.read_text().splitlines()))+' @@\n'+''.join('+'+l+'\n' for l in q.read_text().splitlines())
(B/'NLI_SOURCE_PINS.json').write_text(json.dumps(pins,indent=1));(B/'NLI_NATIVE.patch').write_text(patch)
print('Refreshed own untested native source; root and27 record views share the actual wire backing')
