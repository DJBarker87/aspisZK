from pathlib import Path
import json,hashlib,shutil
B=Path(__file__).resolve().parent;S=B/'NLV_src';n='crates/aspis-r1-cost-probe/src/NLV_native.rs'
pins=json.loads((B/'NLV_SOURCE_PINS.json').read_text());p=S/n
assert hashlib.sha256(p.read_bytes()).hexdigest()==pins[n],'Own native source drift'
old=hashlib.sha256(p.read_bytes()).hexdigest();p.write_text((B/'NLV_native.rs.txt').read_text());pins[n]=hashlib.sha256(p.read_bytes()).hexdigest()
(B/'NLV_SOURCE_PINS.json').write_text(json.dumps(pins,indent=2))
patch=B/'NLV_NATIVE.patch';shutil.copyfile(patch,B/'NLV_NATIVE_before_split2.patch');prefix=patch.read_text().split('--- /dev/null')[0]
patch.write_text(prefix+'--- /dev/null\n+++ b/'+n+'\n@@ -0,0 +1,'+str(len(p.read_text().splitlines()))+' @@\n'+''.join('+'+s+'\n' for s in p.read_text().splitlines()))
(B/'NLV_NATIVE_SPLIT2.json').write_text(json.dumps(dict(before=old,after=pins[n],reason='K007 TIMEOUT retired coupled prepare conjunction. Split error/order, public, scratch windows; bounded u16 observation index covers all57607 cells; arithmetic-free canonical E payload generator; full g footprint retained. No limit or name change.'),indent=2))
print('Corrected own native input; frozen parent and KMX unchanged')
