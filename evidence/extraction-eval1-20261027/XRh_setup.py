from pathlib import Path
import subprocess,json,hashlib,urllib.request,os
B=Path(__file__).resolve().parent
for kind,url in [('releases','https://api.github.com/repos/AeneasVerif/aeneas/releases?per_page=5'),('tags','https://api.github.com/repos/AeneasVerif/aeneas/tags?per_page=10')]:
 data=urllib.request.urlopen(url).read();(B/('XRh_upstream_'+kind+'.json')).write_bytes(data)
# Copy compiler dependency switch out of a stopped image. No container executes.
image='sha256:62b1a46c95d1866f21f76afc23eda952c5b1897da1b6ebbb8650129a9cc64144'
cid=subprocess.check_output(['docker','create',image],text=True).strip()
try:
 subprocess.run(['docker','cp',cid+':/home/opam/.opam/config',str(B/'XRh_opam_config')],check=True)
 print((B/'XRh_opam_config').read_text(),flush=True)
 subprocess.run(['docker','cp',cid+':/home/opam/.opam/5.2',str(B/'XRh_opam')],check=True)
finally:subprocess.run(['docker','rm',cid],check=True)
rows=[]
for n in ['XRh_new_aeneas','XRh_new_charon']:
 S=B/n
 files=subprocess.check_output(['git','ls-files','-z'],cwd=S).decode().split('\0');fs=[]
 for f in filter(None,files):
  p=S/f
  if p.is_file():fs.append(dict(path=f,sha256=hashlib.file_digest(p.open('rb'),'sha256').hexdigest(),bytes=p.stat().st_size))
 rows.append(dict(name=n,revision=subprocess.check_output(['git','rev-parse','HEAD'],cwd=S,text=True).strip(),tree=subprocess.check_output(['git','rev-parse','HEAD^{tree}'],cwd=S,text=True).strip(),files=fs))
(B/'XRh_new_sourcepins.json').write_text(json.dumps(rows,indent=2)+'\n')
print('SOURCE_MANIFEST',[(r['name'],r['revision'],r['tree'],len(r['files'])) for r in rows],flush=True)
print('rust toolchains',subprocess.check_output(['/home/dombarker/.cargo/bin/rustup','toolchain','list'],text=True),flush=True)
