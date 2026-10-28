from pathlib import Path
import json,re,hashlib
R=Path(__file__).resolve().parents[2];E=R/'evidence/pv-runjoin31-20261028';L=R/'docs/research/v8-r0-zk-20261009/lean/R1Z';G=E/'pv31-lane-reference-aeneas-07-generated'
rows=[]
for kind in ['Types','Funs']:
 raw=(G/(kind+'.lean')).read_text()
 expected=raw.replace('import Pv31-lane-reference-names-04.TypesExternal','import R1Z.PV_RunJoin_LaneTypesExternal31').replace('import Pv31-lane-reference-names-04.Types','import R1Z.PV_RunJoin_LaneTypes31').replace('import Pv31-lane-reference-names-04.FunsExternal','import R1Z.PV_RunJoin_LaneExternal31')
 for n in ['PoolV1PairTraceErrorV1','PoolV1PairLeafErrorV1']:expected=expected.replace(n,'PV31_'+n)
 if kind=='Funs':expected=expected.replace('namespace PV_RunJoin_Lane31','namespace PV_RunJoin_Lane31\nvariable [R1Z.BuilderForestAdmissionPort.ExternalLinear]')
 p=L/('PV_RunJoin_Lane'+kind+'31.lean');assert p.read_text()==expected
 rows.append(dict(path=str(p.relative_to(R)),raw_sha256=hashlib.sha256(raw.encode()).hexdigest(),installed_sha256=hashlib.sha256(expected.encode()).hexdigest(),changes='nominal enum names, import paths, explicit ExternalLinear dictionary; no executable body edit'))
raw=(G/'Funs.lean').read_text()
assert re.findall(r'Array.index_usize input.membership.siblings (\d+)#usize',raw)==[str(i) for i in range(20)]
assert re.findall(r'wrapping_shr input.membership.index (\d+)#u32',raw)==[str(i) for i in range(20)]
assert len(re.findall(r'← step ',raw))==20
assert not re.search(r'let\s+\([^\n]*_\)',raw)
# The finite native comparator includes exactly the frozen function body, with a name-only rename.
source=(R/'crates/aspis-statement/src/pool_v1/pair_forest_trace.rs').read_text();a=source.index('fn lane_root(');b=source.index('\nfn temporary_context',a)
body=source[a:b].replace('fn lane_root','fn frozen_lane_root',1)
assert body in (R/'tools/pv-runjoin31-20261028/lane-differential.rs').read_text()
for f in ['TypesExternal','External']:
 s=(L/('PV_RunJoin_Lane'+f+'31.lean')).read_text()
 assert not re.search(r'\b(axiom|sorry|admit|native_decide)\b',s)
(E/'lane-source-audit.json').write_text(json.dumps(dict(emission=rows,parent_steps=20,indices=list(range(20)),fidelity='no iterator/slice mutable borrow, no discarded restoration; scalar local current returned through all twenty steps',native_comparator='name-only copy of exact frozen body; finite validation, not universal equivalence'),indent=2)+'\n')
print('nominal emission, twenty returned parent writes, exact frozen native comparator checked')
