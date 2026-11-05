from pathlib import Path
import shutil,hashlib,json,subprocess
B=Path(__file__).resolve().parent;src=Path('/home/dombarker/project-offloads/codex-cx-extraction-repro1-20261027')
(B/'NHA_bin').mkdir(exist_ok=True)
for n in ['charon','charon-driver','aeneas-b59d5188-extended']:shutil.copy2(src/'XRa_bin'/n,B/'NHA_bin'/n)
# Copy source only, no pre-existing build products or foreign mutable workspace.
shutil.copytree(src/'XRa_toolchain/aeneas',B/'NHA_toolchain/aeneas',ignore=shutil.ignore_patterns('_build','.git'),ignore_dangling_symlinks=True,dirs_exist_ok=True)
inputs={'field':'/home/dombarker/project-offloads/codex-cx-slice-d-field2-20261104/NGA_reference.llbc','queries':'/home/dombarker/project-offloads/codex-cx-transcript-queries-20261105/NGQ_E001.llbc','claim':'/home/dombarker/project-offloads/codex-cx-prepared-claim-20261105/NGU_actual.llbc'}
(B/'NHA_inputs').mkdir(exist_ok=True)
pins={}
for n,p in inputs.items():
 dst=B/'NHA_inputs'/(n+'.llbc');shutil.copy2(p,dst);pins[n]={'origin':p,'sha256':hashlib.sha256(dst.read_bytes()).hexdigest(),'bytes':dst.stat().st_size}
for n in ['charon','charon-driver','aeneas-b59d5188-extended']:
 p=B/'NHA_bin'/n;pins[n]={'sha256':hashlib.sha256(p.read_bytes()).hexdigest(),'bytes':p.stat().st_size}
(B/'NHA_INPUT_PINS.json').write_text(json.dumps(pins,indent=2))
for n,args in [('aeneas',['-help']),('charon',['--help'])]:
 cmd=[str(B/'NHA_bin'/('aeneas-b59d5188-extended' if n=='aeneas' else n)),*args]
 r=subprocess.run(cmd,text=True,capture_output=True);(B/('NHA_'+n+'_help.txt')).write_text(r.stdout+r.stderr);print(n,'help exit',r.returncode)
for n in ['src/interp/InterpReduceCollapse.ml','src/interp/InterpBorrows.ml','src/interp/InterpJoin.ml','src/Config.ml','charon-pin']:
 p=B/'NHA_toolchain/aeneas'/n
 if p.exists():print(n,hashlib.sha256(p.read_bytes()).hexdigest())
print(json.dumps(pins));print(subprocess.check_output(['du','-sh',str(B)],text=True))
