"""Choose actual kernel declaration owners, then check the single module DAG.
No build, proof reduction, or source mutation. Uses bounded header metadata.
"""
import pathlib,json,sys,collections,lzma
V=pathlib.Path('/home/dombarker/project-offloads/codex-pv-lib-slice-20261107/v1-coherence');E=V/'evidence';x=json.load(sys.stdin);plan=json.load(open(V/'PLAN.json'));headers=[json.loads(l) for l in (E/'out-56554.log').read_text().splitlines() if l.startswith('{') and '"declarations"' in l];meta={pathlib.Path(h['path']).stem:h for h in headers};aliases=set(x['canonical_aliases']);allowed=(set(x['modules'])|set(plan['used']))-aliases
owners=collections.defaultdict(set)
for m,h in meta.items():
 if m not in allowed:continue
 for n in set(h['declarations']):owners[n].add(m)
providers={r:sorted(owners[r]) for r in x['roots']};missing={r:ms for r,ms in providers.items() if len(ms)!=1}
assert not missing,missing
heads=sorted({ms[0] for ms in providers.values()});closure=set()
def visit(m):
 if m in closure:return
 closure.add(m)
 for d in meta.get(m,{}).get('imports',[]):visit(d)
for m in heads:visit(m)
assert not closure&aliases,('uncanonical imports',sorted(closure&aliases))
by=collections.defaultdict(set)
for m in closure:
 for n in set(meta.get(m,{}).get('declarations',[])):by[n].add(m)
duplicates={n:sorted(ms) for n,ms in by.items() if len(ms)>1}
report=dict(source_revision=plan['revision'],root_providers={r:ms[0] for r,ms in providers.items()},heads=heads,closure=sorted(closure),duplicate_declarations=duplicates,header_records=len(headers),old_heads=len(x['modules']))
(E/'ROOT_IMPORT_PREFLIGHT.json.xz').write_bytes(lzma.compress(json.dumps(report).encode()));(V/'ROOT_HEADS.json').write_text(json.dumps(heads));print(json.dumps(dict(root_count=len(providers),direct_provider_modules=len(heads),closure_modules=len(closure),pv_lib_in_closure=sum(m.startswith('PV_LIB_') for m in closure),duplicate_declarations=len(duplicates),examples=list(duplicates.items())[:5])))
