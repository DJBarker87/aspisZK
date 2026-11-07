from pathlib import Path
import json,lzma,re,hashlib
E=Path(__file__).resolve().parent;P=E.parent/'ledger25-20261111';C='/home/dombarker/project-offloads/codex-cx-ledger8-cache-20261104/NNI_20261111'
def J(p):return json.loads(lzma.decompress(p.read_bytes()) if p.suffix=='.xz' else p.read_bytes())
def put(n,x):(E/('NNI_'+n+'.json')).write_text(json.dumps(x,indent=1)+'\n')
roots=J(P/'NMQ_AUDIT_ROOTS.json');groups=roots['groups'];allroots=set(roots['roots']);extra=set()
for folder,name in [('tx1-principal-20261111','NNG_C136_AUDIT_ROOTS'),('tx1-principal-20261111','NNG_FOLD_AUDIT_ROOTS'),('lib-20261111','LIB_AUDIT_ROOTS'),('libb-20261111','LIBB_AUDIT_ROOTS'),('libc-20261111','LIBC_AUDIT_ROOTS')]:
 x=J(E.parent/folder/(name+'.json'));extra.update(x.get('roots',[]));extra.update(r for g in x['groups'] for r in g)
# Only accepted revision3 decoder roots, audited by L890/L892.
x=J(E.parent/'tx2-auth-20261111/NMX_AUDIT_ROOTS.json')
for g in x['groups']:
 extra.update(r for r in g if r.startswith('NMX_R3_'))
extra.update(['NMX_R3_DecoderFold.root','NMX_R3_DecoderFold.complete','NMX_R3_DecoderFold.source_eq_reference','NMX_R3_DecoderFold.decode_eq'])
new=sorted(extra-allroots);groups += [new[i:i+80] for i in range(0,len(new),80)];allroots.update(new)
put('AUDIT_ROOTS',dict(roots=sorted(allroots),groups=groups));put('AUDIT_MODULES',[['NNI_COMBINED_IMPORT']]*len(groups))
seeds=[];paths=[]
for folder,name,tag in [('ledger25-20261111','NMQ_EXPORT','NMQ'),('tx2-auth-20261111','NMX_R3_EXPORT','NMX'),('lib-20261111','LIB_BUNDLE_EXPORT','LIB'),('libb-20261111','LIBB_EXPORT','LIBB'),('libc-20261111','LIBC_EXPORT','LIBC')]:
 x=J(E.parent/folder/(name+'.json'));base=x.get('export',x.get('directory'));files=x.get('files',x.get('objects'))
 for r in files:seeds.append(dict(tag=tag,path=r['path'],relative=r['path'][len(base)+1:],sha256=r['sha256'],bytes=r.get('bytes',0)))
 paths.append(C+'/'+tag+'_seed')
x=J(E.parent/'tx1-principal-20261111/NNG_L359/receipt.json')
for r in x['deps_fingerprint']['selected_objects'].values():
 p=r['path'];base=next((a for a in x['env']['LEAN_PATH'].split(':') if p.startswith(a+'/')),None)
 if not base:continue
 # Preserve relative module names while separating original search roots.
 tag='NNG'+str(x['env']['LEAN_PATH'].split(':').index(base));seeds.append(dict(tag=tag,path=p,relative=p[len(base)+1:],sha256=r['sha256'],bytes=0))
for i,root in enumerate(x['env']['LEAN_PATH'].split(':')):
 if any(r['tag']=='NNG'+str(i) for r in seeds):paths.insert(i,C+'/NNG'+str(i)+'_seed')
paths+=J(P/'NMQ_PATHS.json')
paths+=J(E.parent/'tx2-auth-20261111/NMX_R3_ENV.json')['LEAN_PATH'].split(':')
paths+=x['env']['LEAN_PATH'].split(':')+J(E.parent/'lib-20261111/LIB_PATHS.json')+J(E.parent/'libb-20261111/LIBB_PATHS.json')+J(E.parent/'libc-20261111/LIBC_PATHS.json')
put('SEED_INPUTS',seeds);put('PATHS',list(dict.fromkeys(paths)))
(E/'NNI_COMBINED_IMPORT.lean').write_text('import NMQ_COMBINED_IMPORT\nimport NNG_CANDIDATE_COMBINED\nimport NMX_R3_COMBINED_IMPORT\nimport LIB_VLib\nimport LIBC_COMBINED_IMPORT\nimport RPx_Deployed\n#print axioms AspisR1.NNG_Candidate136.candidate\n#print axioms NMX_R3_DecoderFold.root\n#print axioms AspisR1.RPx_Deployed.deployed\n')
for n in ['Driver','OwnerStatements']:(E/('NNI_'+n+'.lean')).write_text((P/('NMQ_'+n+'.lean')).read_text().replace('NMQ_','NNI_'))
expected={json.loads(l)['module']:json.loads(l)['imports'] for l in (P/'NMQ_EXPECTED_IMPORTS.jsonl').read_text().splitlines()}
# New source import inventories, retaining canonical first occurrence order.
for folder in ['tx1-principal-20261111','tx2-auth-20261111','lib-20261111','libb-20261111','libc-20261111']:
 for p in (E.parent/folder).rglob('*.lean'):
  if '/sources/' in str(p):continue
  module=p.stem
  if module in expected:continue
  expected[module]=list(dict.fromkeys(['Init']+re.findall(r'^import\s+([\w.]+)',p.read_text(),re.M)))
for p in Path('docs/research/100bit-spend-path-20261013/lean').glob('RSL*.lean'):expected[p.stem]=list(dict.fromkeys(['Init']+re.findall(r'^import\s+([\w.]+)',p.read_text(),re.M)))
for p in E.glob('NNI_*.lean'):expected[p.stem]=list(dict.fromkeys(['Init']+re.findall(r'^import\s+([\w.]+)',p.read_text(),re.M)))
(E/'NNI_EXPECTED_IMPORTS.jsonl').write_text(''.join(json.dumps(dict(module=m,imports=v))+'\n' for m,v in sorted(expected.items())))
for n in ['run','batch','pin','scope40']:
 s=(P/('NMQ_'+n+'.py')).read_text().replace('NMQ_','NNI_')
 s=s.replace('<=40','<=60').replace("share_info['count']<2","share_info['count']<6").replace("cwd.startswith('/home/dombarker/project-offloads/codex-cx-')","cwd.startswith('/home/dombarker/project-offloads/codex-')")
 s=s.replace("E.parent/'ledger24-20261110/NLX_CLOSURE_PINS.json.xz'","E.parent/'ledger25-20261111/NMQ_CLOSURE_PINS.json.xz'")
 (E/('NNI_'+n+'.py')).write_text(s)
print(json.dumps(dict(roots=len(allroots),extra=len(new),groups=len(groups),seeds=len(seeds))))
