import pathlib,json,subprocess,shlex
P=pathlib.Path(__file__).resolve().parent
manifest=json.loads((P/'source-manifest.json').read_text())
mods=[str(pathlib.Path(x['path']).relative_to('docs/research/v8-r0-zk-20261009/lean')).removesuffix('.lean') for x in manifest]
code='''import pathlib,hashlib,json,sys
B=pathlib.Path('/home/dombarker/project-offloads');P=B/'codex-pv-optb-20261027';O=P/'lean-objects'
rows=[];seen=set()
for m in json.loads(sys.argv[1]):
 s=P/'lean-private'/(m+'.lean')
 imports=[l.split()[1].replace('.','/') for l in s.read_text().splitlines() if l.startswith('import ')]
 for dep in [m]+imports:
  if dep in seen:continue
  seen.add(dep);obj=O/(dep+'.olean')
  rows.append(dict(module=dep,path=str(obj),resolved=str(obj.resolve()),sha256=hashlib.sha256(obj.read_bytes()).hexdigest(),bytes=obj.stat().st_size))
logs={}
for name in ['reservation-44702.json','reservation-44702.log']:
 f=P/name
 if f.exists():logs[name]=f.read_text()
print(json.dumps(dict(objects=rows,logs=logs)))
'''
r=json.loads(subprocess.check_output(['ssh','dombarker@100.108.41.90','python3 -c '+shlex.quote(code)+' '+shlex.quote(json.dumps(mods))],text=True))
for name,s in r.pop('logs').items():(P/('host-'+name)).write_text(s)
(P/'object-manifest.json').write_text(json.dumps(r,indent=2)+'\n')
print('Preserved object hashes (not binaries):',len(r['objects']))
