#!/usr/bin/env python3
"""Read-only shipped-source comparison; no builds or key access."""
import subprocess,hashlib,json
from pathlib import Path
E=Path(__file__).resolve().parent.parent
base=(E/'pins/revision.txt').read_text().strip()
files=subprocess.check_output(['git','ls-files','crates','programs'],text=True).splitlines()
base_files=subprocess.check_output(['git','ls-tree','-r','--name-only',base,'--','crates','programs'],text=True).splitlines()
assert files==base_files
records=[]
for file in files:
 old=subprocess.check_output(['git','show',base+':'+file])
 new=Path(file).read_bytes()
 assert old==new,file
 records.append(dict(path=file,sha256=hashlib.sha256(new).hexdigest(),size=len(new)))
(E/'shipped-sources-unchanged.json').write_text(json.dumps(dict(base_revision=base,compared_revision=subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip(),files=records,all_identical=True,elf_rebuild_triggered=False),indent=2)+'\n')
print(str(len(records))+' shipped source files unchanged.')
