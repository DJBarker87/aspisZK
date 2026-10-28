import pathlib,json,subprocess,os
D=pathlib.Path('/home/dombarker/project-offloads/codex-pv-fscan-20261028');out=[]
for row in json.loads((D/'historical-resolution.json').read_text()):
 if row.get('exit')!=101:continue
 cmd=[x for x in row['argv'] if x!='--offline'];env=dict(os.environ,PATH='/home/dombarker/.cargo/bin:'+os.environ['PATH'],RUSTUP_TOOLCHAIN='1.94.1');r=subprocess.run(cmd,env=env,capture_output=True,text=True);a=dict(path=row['path'],sha256=row['sha256'],prior_exit=101,argv=cmd,exit=r.returncode,stderr=r.stderr)
 if not r.returncode:
  m=json.loads(r.stdout);pk={x['id']:x for x in m['packages']};a['features']=[dict(name=pk[x['id']]['name'],version=pk[x['id']]['version'],features=x['features']) for x in m['resolve']['nodes']]
 out.append(a)
(D/'historical-resolution-recovery.json').write_text(json.dumps(out,indent=2));print([(x['path'],x['exit']) for x in out])
