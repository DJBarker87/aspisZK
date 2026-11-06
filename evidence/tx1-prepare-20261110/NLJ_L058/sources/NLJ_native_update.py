from pathlib import Path
import json,hashlib,difflib
B=Path(__file__).resolve().parent;S=B/'NLJ_src';sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
pins=json.loads((B/'NLJ_SOURCE_PINS.json').read_text());assert all(sha(S/n)==h for n,h in pins.items())
n='crates/aspis-r1-cost-probe/src/NLJ_native.rs';p=S/n;p.write_text((B/'NLJ_native.rs.txt').read_text());pins[n]=sha(p)
(B/'NLJ_SOURCE_PINS.json').write_text(json.dumps(pins,indent=2))
old=(B/'NLJ_NATIVE.patch').read_text();idx=old.index('--- /dev/null\n+++ b/'+n);end=old.find('--- a/',idx+1);end=len(old) if end<0 else end
replacement='--- /dev/null\n+++ b/'+n+'\n@@ -0,0 +1,'+str(len(p.read_text().splitlines()))+' @@\n'+''.join('+'+x+'\n' for x in p.read_text().splitlines())
(B/'NLJ_NATIVE.patch').write_text(old[:idx]+replacement+old[end:])
(B/'NLJ_NATIVE_UPDATE.json').write_text(json.dumps(dict(reason='Add arbitrary full successful136 reply forwarding windows before continuing native runs; K001/K002 superseded',source_sha256=pins[n]),indent=2))
print('Installed successful-reply relay windows; previous error-prefix pair superseded')
