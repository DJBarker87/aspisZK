from PCD_formal import *
a='PCD_E005'
r=run(a,'extraction','Isolated optimized compilation of unchanged frozen aspis-statement for actual extraction', ['python3','PCD_compile_dependency.py'], {'PCD_compile_dependency.py':(E/'PCD_compile_dependency.py').read_text()})
rr=ssh('python3',f'''from pathlib import Path
import json,hashlib
b=Path({B!r});h=hashlib.sha256((b/'PCD_src/Cargo.lock').read_bytes()).hexdigest();assert h=='5782e6a32026fdd95d252d0db7ea20b16716e6deb4f5a397e744886bb6ba22ef'
print(json.dumps({{p.name:p.read_text() for p in b.glob('PCD_E005-*.json')}}))
''');assert rr.returncode==0,rr.stderr
for n,t in json.loads(rr.stdout).items():(E/n).write_text(t)
print('PCD isolated dependency compilation recorded; no extraction eligibility or semantic credit inferred.')
sys.exit(r['exit_status'])
