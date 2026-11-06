from pathlib import Path
import json,hashlib
B=Path(__file__).resolve().parent;S=B/'NLJ_src';sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
pins=json.loads((B/'NLJ_SOURCE_PINS.json').read_text());assert all(sha(S/n)==h for n,h in pins.items())
patch=(B/'NLJ_NATIVE.patch').read_text()
for module in ['NLJ_native','NLJ_factory']:
 n='crates/aspis-r1-cost-probe/src/'+module+'.rs';p=S/n;p.write_text((B/(module+'.rs.txt')).read_text());pins[n]=sha(p)
 idx=patch.index('--- /dev/null\n+++ b/'+n);end=patch.find('--- a/',idx+1);end=len(patch) if end<0 else end
 replacement='--- /dev/null\n+++ b/'+n+'\n@@ -0,0 +1,'+str(len(p.read_text().splitlines()))+' @@\n'+''.join('+'+x+'\n' for x in p.read_text().splitlines())
 patch=patch[:idx]+replacement+patch[end:]
(B/'NLJ_SOURCE_PINS.json').write_text(json.dumps(pins,indent=2));(B/'NLJ_NATIVE.patch').write_text(patch)
(B/'NLJ_PREFIX_SPLIT.json').write_text(json.dumps(dict(reason='K028 retired direct-index/full-log-array shape; selected-record cell only at finish, other cells framed by Lean',files={k:v for k,v in pins.items() if 'NLJ_' in k}),indent=2))
print('Installed selected-record finish window; unchanged frozen parent/callee stubs, same harness names')
