from pathlib import Path
import re,hashlib
r=Path(__file__).resolve().parent
p=r.parent.parent
raw=p/'evidence/session-b-geometry-grouping-callback-20261020/extraction/generated/AspisR1GeometryGrouping/Funs.lean'
assert hashlib.sha256(raw.read_bytes()).hexdigest()=='18e34f9694163248f03ec09a36b43eef71575b44b79e65bc8e2ec241c7771253'
s=raw.read_text();a=s.index('def\n  geometry_groups.closure.Insts.CoreOpsFunctionFnMutTupleUsizeArrayM315.call_mut');b=s.index('\n/--',a);body=s[a:b].split(':= do',1)[1].strip()
body=body.replace('core.array.from_fn','fromFn').replace('geometry_groups.closure.closure.Insts.CoreOpsFunctionFnMutTupleUsizeM31','GroupCallback')
s=(r/'sources/GeometryGroupingOuterModel.lean').read_text();a=s.index('def groupingOuterWithFromFn');b=s.index('\ntheorem geometry_group_outer_total',a);local=s[a:b].split(':= do',1)[1].strip()
norm=lambda s:' '.join(re.findall(r"[A-Za-z_][A-Za-z0-9_'.]*|[0-9]+#[A-Za-z0-9_]+|[0-9]+|[^\s]",s))
assert norm(body)==norm(local)
print('Complete emitted outer callback body, only from_fn parameter/callback alias changed: PASS')
