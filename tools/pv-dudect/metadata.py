#!/usr/bin/env python3
"""Read-only host configuration capture (no timing samples, no policy changes)."""
import pathlib,subprocess,json,sys
O=pathlib.Path(sys.argv[1]);rows={}
for cmd in [['lscpu','-e=CPU,CORE,SOCKET,ONLINE,MAXMHZ'],['uname','-a'],['taskset','-pc',str(__import__('os').getpid())],['ps','-eo','pid,comm,pcpu,rss'],['systemd-cgls','--no-pager']]:
 r=subprocess.run(cmd,text=True,capture_output=True);rows[' '.join(cmd)]=dict(exit=r.returncode,stdout=r.stdout,stderr=r.stderr)
for p in ['/proc/cpuinfo','/sys/kernel/security/lockdown','/proc/sys/kernel/randomize_va_space','/sys/devices/system/cpu/smt/active','/sys/devices/system/cpu/intel_pstate/no_turbo','/sys/devices/system/cpu/cpu2/cpufreq/scaling_governor','/sys/devices/system/cpu/cpu2/topology/thread_siblings_list']:
 try:rows[p]=pathlib.Path(p).read_text()
 except OSError as e:rows[p]=str(e)
for p in pathlib.Path('/sys/class/thermal').glob('thermal_zone*/temp'):
 try:rows[str(p)]=p.read_text()
 except OSError:pass
rows['DOITM']='OFF, V371 retained: no MSR or policy modifications authorized'
(O/'host.json').write_text(json.dumps(rows,indent=2)+'\n')
# Static ruling-(l) evidence: workspace members and ALL direct dependency edges
# of every release program (including default r1-cost-probe).
root=pathlib.Path(__file__).resolve().parents[2]
r=subprocess.run(['/home/dombarker/.cargo/bin/cargo','metadata','--no-deps','--offline','--format-version','1'],cwd=root,text=True,capture_output=True)
assert r.returncode==0,r.stderr
m=json.loads(r.stdout)
release=[p for p in m['packages'] if '/programs/' in p['manifest_path']]
assert all(p['name']!='pv-dudect' for p in m['packages'])
assert not any(d['name'] in ['pv-dudect','source-link'] for p in m['packages'] for d in p['dependencies'])
(O/'release-dependency-isolation.json').write_text(json.dumps(dict(workspace_members=m['workspace_members'],packages=[dict(name=p['name'],manifest_path=p['manifest_path'],dependencies=p['dependencies']) for p in release],harness_in_workspace=False,harness_dependency_edges=[],conclusion='No release program, including programs/r1-cost-probe, can reach either tools-only harness crate; no crates/programs/scripts source changed'),indent=2)+'\n')
for name,path,features in [('candidate','tools/r1-cost-probe/Cargo.toml','r1p-check,aspis-r1-cost-probe/ct-host-prover'),('harness','tools/pv-dudect/Cargo.toml',None)]:
 cmd=['/home/dombarker/.cargo/bin/cargo','metadata','--manifest-path',path,'--offline','--locked','--format-version','1']
 if features:cmd+=['--features',features]
 r=subprocess.run(cmd,cwd=root,text=True,capture_output=True);assert r.returncode==0,r.stderr
 meta=json.loads(r.stdout);pk={p['id']:p for p in meta['packages']}
 selected=[dict(name=pk[x['id']]['name'],version=pk[x['id']]['version'],features=x['features']) for x in meta['resolve']['nodes'] if pk[x['id']]['name'].startswith('aspis') or pk[x['id']]['name'] in ['sha2','zeroize','getrandom','pv-dudect','source-link']]
 (O/(name+'-features.json')).write_text(json.dumps(selected,indent=2)+'\n')
