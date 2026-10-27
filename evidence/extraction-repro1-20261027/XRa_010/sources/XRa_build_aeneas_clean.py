from pathlib import Path
import subprocess,os,hashlib,json
B=Path(__file__).resolve().parent;P=B/'XRa_opam';S=B/'XRa_toolchain'
env=dict(os.environ,PATH=str(P/'bin')+':/usr/bin:/bin',OPAM_SWITCH_PREFIX=str(P),OCAMLLIB=str(P/'lib/ocaml'),OCAMLPATH=str(S/'charon/_build/install/default/lib')+':'+str(P/'lib'),CAML_LD_LIBRARY_PATH=str(P/'lib/stublibs')+':'+str(P/'lib/ocaml/stublibs'),DUNE_CACHE='disabled',AENEAS_VERSION='b59d5188-lean432-extended',OCAMLPARAM='_,ccopt=-static',OCAMLFIND_CONF=str(P/'lib/findlib.conf'))
env.pop('OCAMLPARAM',None)
env['LIBRARY_PATH']=str(B/'XRa_native_libs')
cmds=[(S/'charon',['dune','clean']),(S,['ocamlc','-config']),(S,['ocamlopt','-version']),(S,['dune','--version']),(S,['ocamlfind','query','zarith']),(S/'charon',['dune','build','--profile','release','-j1','--verbose','@install']),(S,['ocamlfind','query','charon']),(S/'aeneas/src',['dune','build','--profile','release','-j1','main.exe'])]
for cwd,cmd in cmds:
 if cwd==S/'aeneas/src':env['OCAMLPARAM']='_,ccopt=-static'
 print('COMMAND',str(cwd),cmd,flush=True);subprocess.run(cmd,cwd=cwd,env=env,check=True)
p=S/'aeneas/src/_build/default/main.exe';v=subprocess.check_output([str(p),'-version'],env=env,text=True).strip()
row={'path':str(p),'sha256':hashlib.file_digest(p.open('rb'),'sha256').hexdigest(),'bytes':p.stat().st_size,'version':v,'source_tree':'5a843e70672e4139232b2fdcb52a0c1fbd4b1619','dependency_image':'sha256:ef96e46342a4159b6a62663e1ff5474a5f5deaf260daf08ea7b0963974418db7'}
print(json.dumps(row),flush=True);(B/'XRa_aeneas_outputs.json').write_text(json.dumps(row,indent=2)+'\n')
