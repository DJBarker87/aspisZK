from pathlib import Path
import json,hashlib,shutil
B=Path(__file__).resolve().parent;S=B/'NLV_src';n='crates/aspis-r1-cost-probe/src/NLV_native.rs'
pins=json.loads((B/'NLV_SOURCE_PINS.json').read_text());p=S/n
assert hashlib.sha256(p.read_bytes()).hexdigest()==pins[n],'Own native source drift'
old=hashlib.sha256(p.read_bytes()).hexdigest();p.write_text((B/'NLV_native.rs.txt').read_text());pins[n]=hashlib.sha256(p.read_bytes()).hexdigest()
(B/'NLV_SOURCE_PINS.json').write_text(json.dumps(pins,indent=2))
patch=B/'NLV_NATIVE.patch';shutil.copyfile(patch,B/'NLV_NATIVE_before_windows.patch');prefix=patch.read_text().split('--- /dev/null')[0]
patch.write_text(prefix+'--- /dev/null\n+++ b/'+n+'\n@@ -0,0 +1,'+str(len(p.read_text().splitlines()))+' @@\n'+''.join('+'+s+'\n' for s in p.read_text().splitlines()))
(B/'NLV_NATIVE_WINDOWS.json').write_text(json.dumps(dict(before=old,after=pins[n],reason='Isolate fourteen independent source occurrences after two retired coupled shapes. Full physical producer and callee installation remain OPEN. No frozen source, caps or timeout change.'),indent=2))
print('Corrected own native input; frozen parent and KMX unchanged')
