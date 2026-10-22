"""Verify the rebuilt ELF source snapshot against every tracked shipped file."""
from pathlib import Path
import json,hashlib,subprocess
E=Path(__file__).resolve().parent.parent
files=subprocess.check_output(['git','ls-files','crates','programs','.cargo','Cargo.toml','Cargo.lock'],text=True).splitlines()
pins={p:dict(sha256=hashlib.sha256(Path(p).read_bytes()).hexdigest(),size_bytes=Path(p).stat().st_size) for p in files}
code='''from pathlib import Path
import sys,json,hashlib
root=Path('/home/dombarker/project-offloads/codex-cx-prover-commit29-20261022/frozen-src')
pins=json.load(sys.stdin)
diffs=[]
for name,want in pins.items():
 p=root/name
 got=dict(sha256=hashlib.sha256(p.read_bytes()).hexdigest(),size_bytes=p.stat().st_size) if p.exists() else None
 if got!=want:diffs.append(dict(path=name,want=want,got=got))
print(json.dumps(dict(checked_files=len(pins),differences=diffs)))
'''
# Keep shell text fixed; file paths and hashes pass as JSON on stdin.
remote=['ssh','dombarker@100.108.41.90','python3 -c '+"'"+code.replace("'","'\\''")+"'"]
r=subprocess.run(remote,input=json.dumps(pins),text=True,capture_output=True,check=True)
result=json.loads(r.stdout);assert result['differences']==[],result
receipt=dict(source_revision=subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip(),pins=pins,result=result,source_identity='base revision 495b8640a plus exact source pins; the cfg-only finite helper is committed after validation',artifacts='frozen-elf-final-check.json',scope='all tracked crates/programs files plus Cargo manifest/lock and .cargo configuration; exact source bytes, no binaries')
(E/'frozen-source-inventory.json').write_text(json.dumps(receipt,indent=2)+'\n')
print(result)
