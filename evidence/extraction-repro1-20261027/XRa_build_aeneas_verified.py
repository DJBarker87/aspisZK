from pathlib import Path
import subprocess,json,hashlib
B=Path(__file__).resolve().parent;S=B/'XRa_toolchain/aeneas'
audit=json.loads((B/'XRa_historical_extended-tool-audit.json').read_text())
# Normalize the ephemeral git index to source files only; do not include
# task-local Dune outputs in a source tree hash.
subprocess.run(['git','read-tree','5a843e70672e4139232b2fdcb52a0c1fbd4b1619'],cwd=S,check=True)
subprocess.run(['git','add','--',*audit['exact_changed_files']],cwd=S,check=True)
tree=subprocess.check_output(['git','write-tree'],cwd=S,text=True).strip()
changed=set(subprocess.check_output(['git','diff','--name-only','5a843e70672e4139232b2fdcb52a0c1fbd4b1619',tree],cwd=S,text=True).splitlines())
assert changed==set(audit['exact_changed_files'])
assert all(hashlib.sha256((S/p).read_bytes()).hexdigest()==h for p,h in audit['exact_changed_files'].items())
assert tree=='3be6820e84debbb8f2cc6b61abca478e98157bc7',tree
result={'source_tree':tree,'all_38_historical_file_pins_match':True,'no_other_source_change':True,'contradicts_recipe_expected_tree':audit['build_recipe_expected_tree']}
(B/'XRa_verified_extended_source.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result),flush=True)
from pathlib import Path
import subprocess,os,hashlib,json
B=Path(__file__).resolve().parent;P=B/'XRa_opam';S=B/'XRa_toolchain'
env=dict(os.environ,PATH=str(P/'bin')+':/usr/bin:/bin',OPAM_SWITCH_PREFIX=str(P),OCAMLLIB=str(P/'lib/ocaml'),OCAMLPATH=str(S/'charon/_build/install/default/lib')+':'+str(P/'lib'),CAML_LD_LIBRARY_PATH=str(P/'lib/stublibs')+':'+str(P/'lib/ocaml/stublibs'),DUNE_CACHE='disabled',AENEAS_VERSION='b59d5188-lean432-extended',OCAMLPARAM='_,ccopt=-static',OCAMLFIND_CONF=str(P/'lib/findlib.conf'))
env.pop('OCAMLPARAM',None)
env['LIBRARY_PATH']=str(B/'XRa_native_libs')
cmds=[(S,['ocamlopt','-version']),(S,['dune','--version']),(S,['ocamlfind','query','zarith']),(S/'charon',['dune','build','--profile','release','-j1','@install']),(S,['ocamlfind','query','charon']),(S/'aeneas/src',['dune','build','--profile','release','-j1','main.exe'])]
for cwd,cmd in cmds:
 if cwd==S/'aeneas/src':env['OCAMLPARAM']='_,ccopt=-static'
 print('COMMAND',str(cwd),cmd,flush=True);subprocess.run(cmd,cwd=cwd,env=env,check=True)
p=S/'aeneas/src/_build/default/main.exe';v=subprocess.check_output([str(p),'-version'],env=env,text=True).strip()
row={'path':str(p),'sha256':hashlib.file_digest(p.open('rb'),'sha256').hexdigest(),'bytes':p.stat().st_size,'version':v,'source_tree':'3be6820e84debbb8f2cc6b61abca478e98157bc7','dependency_image':'sha256:ef96e46342a4159b6a62663e1ff5474a5f5deaf260daf08ea7b0963974418db7'}
print(json.dumps(row),flush=True);(B/'XRa_aeneas_corrected_outputs.json').write_text(json.dumps(row,indent=2)+'\n')
