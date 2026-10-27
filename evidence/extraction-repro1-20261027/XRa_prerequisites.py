import pathlib,subprocess,json,hashlib,shutil
r=pathlib.Path('/home/dombarker/project-offloads')
for name in ['docker','opam','ocamlopt','dune','cargo','git']:
 print('TOOL',name,shutil.which(name))
for cmd in [['df','-h',str(r)],['docker','image','ls','--no-trunc','--format','{{.ID}} {{.Repository}}:{{.Tag}} {{.Digest}}'],['docker','info','--format','{{.CgroupDriver}} {{.CgroupVersion}}']]:
 print('COMMAND',cmd)
 try:
  p=subprocess.run(cmd,capture_output=True,text=True,timeout=25);print(p.returncode,p.stdout,p.stderr)
 except Exception as e:print(type(e).__name__,str(e))
for q in [r/'s4-fromfn-guard-inline-charon-v1-20261022/inputs/aeneas-exact-source.tar.gz',r/'s4-fromfn-guard-inline-charon-v1-20261022/inputs/charon-exact-source.tar.gz',r/'ZK-v7-aeneas-return-test-20260828/aeneas-verif/lean432/aeneas-b59d5188-lean432.patch']:
 print('INPUT',str(q),q.exists(),hashlib.file_digest(q.open('rb'),'sha256').hexdigest() if q.is_file() else None)
for p in [pathlib.Path('/home/dombarker/.opam'),r/'s4-fromfn-guard-inline-charon-v1-20261022',r/'s5-charon-selfid-repair-v1']:
 print('DIR',str(p),[x.name for x in p.iterdir()] if p.is_dir() else None)
