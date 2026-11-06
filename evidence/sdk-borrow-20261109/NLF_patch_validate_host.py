from pathlib import Path
import json,hashlib,subprocess
B=Path.cwd();p=B/'NLF_native_packets.patch';x=json.loads((B/'NLF_PATCH_IDENTITY.json').read_text())
assert hashlib.sha256(p.read_bytes()).hexdigest()==x['patch_sha256']
source=''.join(l[1:] for l in p.read_text().split('+++ b/programs/r1-cost-probe/src/NLF_sdk.rs\n',1)[1].splitlines(True) if l.startswith('+'))
assert hashlib.sha256(source.encode()).hexdigest()==x['harness_sha256']
assert (B/'NLF_src/programs/r1-cost-probe/src/NLF_sdk.rs').read_text()==source
r=subprocess.run(['patch','--dry-run','--reverse','-p1','-i',str(p)],cwd=B/'NLF_src',capture_output=True,text=True)
assert r.returncode==0,r.stdout+r.stderr
(B/'NLF_PATCH_VALIDATION.json').write_text(json.dumps(dict(exit=r.returncode,stdout=r.stdout,stderr=r.stderr,source_matches_last_native_receipt=True,patch_sha256=x['patch_sha256'],CARGO_TARGET_DIR=str(B/'NLF_target')),indent=1)+'\n')
print('NLF harness patch reverse-dry-run passed against the exact final native scratch inputs')
