from pathlib import Path
import json,hashlib
R=Path(__file__).resolve().parents[2];E=R/'evidence/pv-runjoin30-20261028';L=R/'docs/research/v8-r0-zk-20261009/lean/R1Z';G=E/'pv30-outer-aeneas-03-generated'
renames=['PoolV1PaymentStatementFormatError','PoolV1PairLeafErrorV1','PoolV1PairTraceErrorV1'];rows=[]
for kind in ['Types','Funs']:
 raw=(G/(kind+'.lean')).read_text();expected=raw.replace('import Pv30-outer-names-02.TypesExternal','import R1Z.PV_RunJoin_OuterTypesExternal30').replace('import Pv30-outer-names-02.Types','import R1Z.PV_RunJoin_OuterTypes30').replace('import Pv30-outer-names-02.FunsExternal','import R1Z.PV_RunJoin_OuterExternal30')
 if kind=='Funs':expected=expected.replace('namespace PV_RunJoin_Outer30','namespace PV_RunJoin_Outer30\nvariable [LaneRoot] [R1Z.BuilderForestAdmissionPort.ExternalLinear] [R1Z.BuilderForestAdmissionPort.Records]')
 for v in renames:expected=expected.replace(v,'PV30_'+v)
 p=L/('PV_RunJoin_Outer'+kind+'30.lean');assert p.read_text()==expected,p
 rows.append(dict(path=str(p.relative_to(R)),raw_sha256=hashlib.sha256(raw.encode()).hexdigest(),installed_sha256=hashlib.sha256(expected.encode()).hexdigest(),modifications='import paths; uniquely prefixed enum names; explicit external dictionaries in Funs only; executable bodies otherwise byte-identical'))
x=json.loads((E/'pv30-outer-charon-02.llbc').read_text());y=json.loads((E/'pv30-outer-names-02.llbc').read_text());changes=json.loads((E/'constructor-renames.json').read_text())
for c in changes['changes']:next(r for r in y['translated']['fun_decls'] if r and r['def_id']==c['id'])['item_meta']['attr_info']['rename']=c['old']
assert x==y
roots=[]
for r in x['translated']['fun_decls']:
 if not r:continue
 name=str(r['item_meta']['name'])
 if any(t in name for t in ['compile_pool_v1_pair_forest_','lane_root','validate_common','compile_forest_from_copies']):
  m=r['item_meta'];present=isinstance(r['body'],dict)
  row=dict(name=m['name'],id=r['def_id'],body_present=present,body_kind='Structured' if present else r['body'])
  if present:
   text=m['source_text'];source=R/('crates/aspis-statement/src/pool_v1/'+('payment_relation.rs' if 'payment_relation' in name else 'pair_forest_trace.rs'))
   assert text in source.read_text(),m['name'];row.update(source=str(source.relative_to(R)),source_text_sha256=hashlib.sha256(text.encode()).hexdigest())
  roots.append(row)
(E/'outer-source-association-audit.json').write_text(json.dumps(dict(installed=rows,llbc_metadata_only=True,functions=roots,unresolved_native_law='lane_root; quantified callback has no success assumption; no native closure inferred from template filling'),indent=2)+'\n')
(E/'outer-llbc-preflight.json').write_text(json.dumps(dict(has_errors=x['has_errors'],roots=roots,llbc_sha256=hashlib.sha256((E/'pv30-outer-charon-02.llbc').read_bytes()).hexdigest()),indent=2)+'\n')
print('outer source and nominal-only emission changes checked')
