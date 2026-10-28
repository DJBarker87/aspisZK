from pathlib import Path
import subprocess,json,os,hashlib,tomllib
h=Path('/home/dombarker/project-offloads/codex-cx-native-featparity-20261028')
env=dict(os.environ,PATH='/home/dombarker/.cargo/bin:/usr/bin:/bin',CARGO_NET_OFFLINE='true')
cases=[{'manifest': '/home/dombarker/project-offloads/codex-cx-native-prepare4-20261028/NCA_src/crates/aspis-r1-cost-probe/Cargo.toml', 'features': '', 'no_default': False, 'receipts': ['NCA_*']}, {'manifest': '/home/dombarker/project-offloads/codex-cx-kani-mitig-20261028/KMX_src/crates/aspis-r1-cost-probe/Cargo.toml', 'features': '', 'no_default': False, 'receipts': ['KMX_*']}]
for i,c in enumerate(cases):
 m=Path(c['manifest'])
 if not m.exists():print(json.dumps(dict(case=i,exists=False,**c)));continue
 t=tomllib.loads(m.read_text());d=h/('NCS_extra_'+str(i));d.mkdir(exist_ok=True)
 dep=dict(package=t['package']['name'],path=str(m.parent),features=c['features'].split(',') if c['features']else [])
 s='[package]\nname="ncs-historical-root"\nversion="0.0.0"\nedition="2021"\n[workspace]\n[lib]\npath="empty.rs"\n[dependencies.ncs-target]\n'
 for k,v in dep.items():s+=k+'='+json.dumps(v)+'\n'
 if c['no_default']:s+='default-features=false\n'
 (d/'Cargo.toml').write_text(s);(d/'empty.rs').write_text('')
 ancestors=[q for q in m.parents if (q/'Cargo.lock').exists()]
 if ancestors:(d/'Cargo.lock').write_bytes((ancestors[0]/'Cargo.lock').read_bytes())
 cmd=['cargo','metadata','--offline','--format-version','1','--manifest-path',str(d/'Cargo.toml')]
 r=subprocess.run(cmd,env=env,capture_output=True,text=True,cwd=d)
 out=dict(case=i,exists=True,command=cmd,exit=r.returncode,stderr=r.stderr,root_manifest=m.read_text(),root_manifest_sha256=hashlib.sha256(m.read_bytes()).hexdigest(),**c)
 if r.returncode==0:
  j=json.loads(r.stdout);pk={p['id']:p for p in j['packages']}
  out['nodes']=[dict(id=n['id'],name=pk[n['id']]['name'],version=pk[n['id']]['version'],features=n['features'])for n in j['resolve']['nodes']]
  out['local_manifests']={p['manifest_path']:Path(p['manifest_path']).read_text() for p in j['packages'] if p['source']is None and p['name']!='ncs-historical-root'}
 print(json.dumps(out))
