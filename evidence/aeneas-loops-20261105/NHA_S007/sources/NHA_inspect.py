from pathlib import Path
import subprocess,json,hashlib,shutil
B=Path(__file__).resolve().parent
for name,cmd in [('aeneas_version',[str(B/'NHA_bin/aeneas-b59d5188-extended'),'-version']),('charon_version',[str(B/'NHA_bin/charon'),'version']),('charon_toolchain',[str(B/'NHA_bin/charon'),'toolchain-version']),('charon_cargo_help',[str(B/'NHA_bin/charon'),'cargo','--help'])]:
 r=subprocess.run(cmd,text=True,capture_output=True);(B/('NHA_'+name+'.txt')).write_text(r.stdout+r.stderr);print(name,r.returncode,r.stdout[:500])
src=B/'NHA_toolchain/aeneas';out=B/'NHA_source_inspection';out.mkdir(exist_ok=True)
for p in ['src/interp/InterpReduceCollapse.ml','src/interp/InterpBorrows.ml','src/interp/InterpJoin.ml','src/Config.ml','src/Main.ml','src/pure/PureMicroPasses.ml','src/pure/PureMicroPassesLoops.ml']:
 shutil.copy2(src/p,out/Path(p).name)
patch=Path('/home/dombarker/project-offloads/aeneas-d860ac47-preserve-distinct-loop-input-abstractions.patch');shutil.copy2(patch,out/('NHA_PRECEDENT_'+patch.name))
pins={str(p.relative_to(B)):hashlib.sha256(p.read_bytes()).hexdigest() for p in out.rglob('*') if p.is_file()}
(B/'NHA_SOURCE_INSPECTION.json').write_text(json.dumps(pins,indent=2))
print(subprocess.check_output(['du','-sh',str(B)],text=True))
