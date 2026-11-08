"""Freeze/recheck the complete single LEAN_PATH, including companion files."""
import pathlib,hashlib,json,lzma,sys,time,subprocess
V=pathlib.Path('/home/dombarker/project-offloads/codex-pv-lib-slice-20261107/v1-coherence');E=V/'evidence';O=V/'objects-resolved';mode=sys.argv[1];sha=lambda p:hashlib.file_digest(open(p,'rb'),'sha256').hexdigest()
p=E/'COHORT_FREEZE.json.xz'
if mode=='freeze':
 assert not p.exists()
 env=json.load(open(V/'J.json'));actual=subprocess.check_output([env['LEAN'],'--githash'],text=True).strip();assert actual==env['LEAN_GITHASH']
 files={str(q.relative_to(O)):dict(path=str(q.resolve()),bytes=q.stat().st_size,sha256=sha(q)) for q in O.rglob('*') if q.is_file()}
 sources={str(q.relative_to(V/'sources')):sha(q) for q in (V/'sources').glob('*.lean')}
 data=dict(revision=json.load(open(V/'PLAN.json'))['revision'],epoch=time.time(),files=files,sources=sources,env_sha256=sha(V/'J.json'),lean_githash=actual,lean_binary_sha256=sha(env['LEAN']))
 p.write_bytes(lzma.compress(json.dumps(data).encode()));print('Frozen',len(files),'object and companion files;',len(sources),'sources')
elif mode=='check':
 data=json.loads(lzma.decompress(p.read_bytes()));assert sha(V/'J.json')==data['env_sha256']
 for name,v in data['files'].items():assert sha(O/name)==v['sha256'],('object changed',name)
 for name,h in data['sources'].items():assert sha(V/'sources'/name)==h,('source changed',name)
 (E/'COHORT_FREEZE_CHECK.json').write_text(json.dumps(dict(unchanged=True,object_files=len(data['files']),sources=len(data['sources']),freeze_sha256=sha(p)),indent=2));print('All frozen object, companion and source hashes unchanged')
else:raise RuntimeError(mode)
