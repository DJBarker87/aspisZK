from NBW_host import *
import hashlib
admit('NBW_IMPORT001')
r=py('''from pathlib import Path
import hashlib,json,shutil
old=Path('/home/dombarker/project-offloads/codex-cx-kmx-cache-20261028/KMX_CopyMeaning.olean')
source=Path('/home/dombarker/project-offloads/codex-cx-kani-mitig-20261028/KMX_CopyMeaning.lean')
expected='2baec49a3446a3bbb2be6f992c97d0a6897534a1cd308db8746194dedf665f2b'
assert hashlib.sha256(source.read_bytes()).hexdigest()==expected
new=Path('/home/dombarker/project-offloads/codex-cx-query-cache-20261028/KMX_CopyMeaning.olean')
assert not new.exists()
shutil.copyfile(old,new)
print(json.dumps(dict(source=str(source),source_sha256=expected,object=str(old),object_sha256=hashlib.sha256(old.read_bytes()).hexdigest(),destination=str(new),destination_sha256=hashlib.sha256(new.read_bytes()).hexdigest(),receipt='evidence/kani-mitig-20261028/KMX_L003/receipt.json')))
''')
assert r.returncode==0,r.stderr
(E/'NBW_KMX_IMPORT.json').write_text(r.stdout)
