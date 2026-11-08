"""Stage only job evidence; omit transient guards and ignored build outputs."""
from pathlib import Path
import subprocess,sys
E=Path(__file__).resolve().parent;rel=E.relative_to(Path.cwd());msg=sys.argv[1]
for p in E.rglob('*'):
 if p.is_file()and p.name!='NNL_CLIENT_ACTIVE':assert p.stat().st_size<=20_000_000,p
subprocess.run(['git','add','-u','--',str(rel)],check=True)
x=subprocess.check_output(['git','ls-files','--others','--exclude-standard','-z','--',str(rel)]).split(b'\0');x=[p for p in x if p and not p.endswith((b'/NNL_CLIENT_ACTIVE',b'/NNL_HOLD'))]
assert not any(p.endswith((b'.olean',b'.ir',b'.pyc',b'.elf'))for p in x)
if x:subprocess.run(['git','add','--pathspec-from-file=-','--pathspec-file-nul'],input=b'\0'.join(x)+b'\0',check=True)
subprocess.run(['git','commit','--quiet','-m',msg],check=True)
