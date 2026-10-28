import pathlib,json,os,subprocess,hashlib
D=pathlib.Path('/home/dombarker/project-offloads/codex-pv-fscan-20261028');rows=json.loads((D/'historical-manifests.json').read_text());out=[]
for m in rows:
 p=pathlib.Path(m['path'])
 if not (p.parent/'Cargo.lock').exists():
  out.append(dict(path=str(p),sha256=m['sha256'],status='no retained lock; metadata not run to avoid writing historical workspace'));continue
 env=dict(os.environ,PATH='/home/dombarker/.cargo/bin:'+os.environ['PATH'],RUSTUP_TOOLCHAIN='1.94.1')
 cmd=['cargo','metadata','--format-version','1','--locked','--offline','--manifest-path',str(p)];r=subprocess.run(cmd,env=env,capture_output=True,text=True)
 row=dict(path=str(p),sha256=m['sha256'],argv=cmd,exit=r.returncode,stderr=r.stderr)
 if not r.returncode:
  a=json.loads(r.stdout);pk={x['id']:x for x in a['packages']};row['features']=[dict(name=pk[x['id']]['name'],version=pk[x['id']]['version'],id=x['id'],features=x['features']) for x in a['resolve']['nodes']]
 out.append(row)
(D/'historical-resolution.json').write_text(json.dumps(out,indent=2));print('historical graphs',len(out),'successes',sum(x.get('exit')==0 for x in out))
