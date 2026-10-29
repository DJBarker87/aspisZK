from pathlib import Path
import json,lzma,hashlib,re,collections
D=Path('/home/dombarker/project-offloads/codex-pv-diag8-20261029');R=D.parent/'codex-pv-rdea-20261028'
with lzma.open(R/'ir-unit-qualified-graph.json.xz','rt') as f:g=json.load(f)
reach=set(g['reachable']);names=g['names'];print('reach',len(reach),'linked',len(g['linked']));print('types',type(g['reachable']),type(g['linked']))
lognames=[(k,v) for k,v in names.items() if any(s in v for s in ['log::__private','log::logger','log::max_level','Log>::log'])]
print('logger targets',lognames[:30])
rows=json.loads((D/'logger-ir-sites.json').read_text()); out=[]
for r in rows:
 if r['kind']=='mir':continue
 # Report exact caller candidates and whether the inherited direct graph reaches the target.
 r['target_reachable_in_inherited_graph']=r.get('target') in reach or any(k.endswith('::'+r.get('target','NONE')) for k in reach)
 out.append(r)
(D/'logger-reachability.json').write_text(json.dumps(dict(graph_sha256=hashlib.sha256((R/'ir-unit-qualified-graph.json.xz').read_bytes()).hexdigest(),targets=lognames,sites=out,complete=False,reason='direct graph omits opaque indirect calls; linked presence is not honest reachability'),indent=2)+'\n')
c=collections.Counter(r['function'] for r in out);print('logger LLVM callers',c)
# Only retained, coherent project objects; every transitive fingerprint is checked.
P=D.parent/'codex-pv-diag5-20261029'; x=json.loads((P/'final-post.json').read_text())['rows']; needed={};sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
def visit(m):
 if m in needed:return
 q=x[m];p=Path(q['path']);assert sha(p)==q['sha256'],m;needed[m]=q
 for dep,vals in q.get('dependencies',{}).items():
  visit(dep);assert next(v for path,v in vals.items() if path.endswith('.olean'))==needed[dep]['sha256']
visit('R1Z.ProverCommitArrayIndex25')
for m,q in needed.items():
 if q.get('source_sha256'):
  src=Path(q['path']);dst=D/'objects'/(m.replace('.','/')+'.olean');dst.parent.mkdir(parents=True,exist_ok=True);dst.symlink_to(src)
  for a,b in [(Path(str(src)+'.server'),Path(str(dst)+'.server')),(Path(str(src)+'.private'),Path(str(dst)+'.private')),(src.with_suffix('.ir'),dst.with_suffix('.ir'))]:
   if a.is_file():b.symlink_to(a)
(D/'reuse.json').write_text(json.dumps(dict(rows=needed,checked=len(needed),same_toolchain='lean4:v4.32.0',same_effective_prefix='private objects then identical runjoin32 external; every selected object identical',boundary='h6 read-only reuse; no shared source edited'),indent=2)+'\n');print('reused closure',len(needed))
