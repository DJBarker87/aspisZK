from pathlib import Path
import os,subprocess,json,hashlib
B=Path(__file__).resolve().parent;P=B/'XRh_opam';C=B/'XRh_new_charon';A=B/'XRh_new_aeneas'
(P/'lib/findlib.conf').write_text(f'destdir="{P}/lib"\npath="{P}/lib/ocaml:{P}/lib"\nocamlc="ocamlc.opt"\nocamlopt="ocamlopt.opt"\nocamldep="ocamldep.opt"\nocamldoc="ocamldoc.opt"\n')
if not (A/'charon').exists():(A/'charon').symlink_to(C,target_is_directory=True)
# Charon vendored by dune via src/charon symlink in upstream source.
print('CHARON_LINK',str(A/'src/charon'),(A/'src/charon').is_symlink(),flush=True)
env=dict(os.environ,PATH=str(P/'bin')+':/usr/bin:/bin',OPAM_SWITCH_PREFIX=str(P),OCAMLLIB=str(P/'lib/ocaml'),OCAMLPATH=str(C/'_build/install/default/lib')+':'+str(P/'lib'),CAML_LD_LIBRARY_PATH=str(P/'lib/stublibs')+':'+str(P/'lib/ocaml/stublibs'),DUNE_CACHE='disabled',OCAMLFIND_CONF=str(P/'lib/findlib.conf'),AENEAS_VERSION='472b3d560cf236db50f38ad421eb0a88b57a1580')
L=B/'XRh_native_libs';L.mkdir(exist_ok=True)
for name,src in [('zstd','/lib/x86_64-linux-gnu/libzstd.so.1'),('gmp','/lib/x86_64-linux-gnu/libgmp.so.10')]:
 p=L/('lib'+name+'.so')
 if not p.exists():p.symlink_to(src)
env['LIBRARY_PATH']=str(L)
for cwd,cmd in [(C,['make','charon-ml/src/CharonVersion.ml']),(C,['dune','build','--profile','release','-j1','@install']),(A/'src',['dune','build','--profile','release','-j1','main.exe'])]:
 print('COMMAND',str(cwd),cmd,flush=True);subprocess.run(cmd,cwd=cwd,env=env,check=True)
p=A/'src/_build/default/main.exe'
r=dict(path=str(p),sha256=hashlib.file_digest(p.open('rb'),'sha256').hexdigest(),bytes=p.stat().st_size,version=subprocess.check_output([str(p),'-version'],env=env,text=True))
(B/'XRh_new_aeneas_binary.json').write_text(json.dumps(r,indent=2)+'\n');print(json.dumps(r),flush=True)
