#!/usr/bin/env python3
"""Preserve13/45/proof variants with old provenance and355 actual-Name alternatives."""
import collections,json,pathlib,resource,sqlite3,subprocess,time
from Port31DATA_run import T,E,pin,state,safe
start=time.monotonic();schema=json.loads((E/'Port31DATA_variants-schema355.json').read_text());p=safe(schema['historical_input']['path']);before=state(p);assert pin(p)==schema['historical_input']
x=json.loads(p.read_text());rows=x['comparisons'];oc=[r for r in rows if r['tag']=='full-original-current'];by=collections.defaultdict(list)
for r in oc:
 if r['strict_v3']:continue
 if r['sameDeclaration']:k='alpha_equal_strict_different'
 elif r['strict_type'] and r['proof_only_same_full_type']:k='strict_type_theorem_proof_variant'
 else:k='declaration_conflict'
 by[k].append(r)
counts={k:len({r['name'] for r in v}) for k,v in by.items()};assert counts==dict(alpha_equal_strict_different=45,strict_type_theorem_proof_variant=4,declaration_conflict=13),counts
out=pathlib.Path('/private/tmp/Port31DATA-355-20261025');dbp=safe(out/'Port31DATA_inventory355.sqlite');dbbefore=state(dbp);dbpin=pin(dbp);db=sqlite3.connect('file:'+str(dbp)+'?mode=ro',uri=True)
def key(x):return json.dumps(x,separators=(',',':'),ensure_ascii=False)
data=[]
for category,rs in by.items():
 for display in sorted({r['name'] for r in rs}):
  actual=list(db.execute('SELECT name,origin,kind,value FROM constant WHERE display=? ORDER BY name,origin',(display,)))
  names=sorted({n for n,o,k,v in actual});pairs=[]
  for n in names:
   pairs += [dict(actual_name=json.loads(n),left=a,right=b,strict=bool(s),strict_type=bool(t),strict_value=bool(v),strict_rules=bool(u)) for a,b,s,t,v,u in db.execute('SELECT left_origin,right_origin,strict,strict_type,strict_value,strict_rules FROM pair WHERE name=?',(n,))]
  data.append(dict(category=category,presentation_label=display,historical_observations=[r for r in rs if r['name']==display],actual_names=[json.loads(n) for n in names],actual_variants=[dict(name=json.loads(n),origin=o,kind=k,has_value=bool(v)) for n,o,k,v in actual],new_strict_pair_receipts=pairs,selection='NONE; no printed-label-to-Name reconstruction or alpha-as-literal inference'))
report=dict(status='HISTORICAL VARIANTS RETAINED;355 ACTUAL-NAME MAP ONLY',command=['python3','-B',str(pathlib.Path(__file__))],source=pin(__file__),source_revision=subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip(),historical_input=pin(p),inventory_input=dbpin,historical_counts=counts,historical_observations=len(oc),categories=data,assertion='All13 definition conflicts,45 representation differences and4 strict-type proof-variant names preserved with full historical provenance. Matching printed labels discover actual-Name alternatives only; no origin selection/equivalence theorem.',print_axioms='N/A: noncompiler; Bool353 audit REUSED',lean_calls=0,pre_post_stat_unchanged=state(p)==before and state(dbp)==dbbefore,wall_seconds=time.monotonic()-start,peak_rss_bytes=resource.getrusage(resource.RUSAGE_SELF).ru_maxrss,swaps=resource.getrusage(resource.RUSAGE_SELF).ru_nswap,exit_status=0)
assert report['pre_post_stat_unchanged'];dest=out/'Port31DATA_variant-map355.json';dest.write_text(json.dumps(report,indent=2,ensure_ascii=False)+'\n')
if dest.stat().st_size<=5_000_000:(E/'Port31DATA_variant-map355.json').write_bytes(dest.read_bytes())
else:(E/'Port31DATA_variant-map355.json').write_text(json.dumps(dict(external_payload=pin(dest),historical_counts=counts,source=pin(__file__),command=report['command'],source_revision=report['source_revision'],exit_status=0,wall_seconds=report['wall_seconds'],peak_rss_bytes=report['peak_rss_bytes'],swaps=report['swaps'],lean_calls=0,axioms='N/A'),indent=2)+'\n')
print(json.dumps(dict(historical_counts=counts,new_lean_calls=0,output=pin(dest),wall_seconds=report['wall_seconds'],peak_rss_bytes=report['peak_rss_bytes'])))
