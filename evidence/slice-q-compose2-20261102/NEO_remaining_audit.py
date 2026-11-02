"""Recompute exact remaining Q rows and edges without granting any credit."""
from pathlib import Path
import json,hashlib
E=Path(__file__).resolve().parent;R=E.parent.parent
load=lambda p:json.loads(p.read_text());b=load(R/'evidence/ledger4-20261102/NEN_LEDGER.json');d=load(E/'NEO_LEDGER_DELTA.json');edges=load(E/'NEO_EDGES.json')['edges'];q=load(R/'docs/research/100bit-spend-path-20261013/design/VERTICAL-SLICES-20261029.json')['slices']['Q']
closed={r['function'] for r in b['rows'] if r['composed_status']=='CLOSED' or r['row'] in d['newly_closed']}
reasons={
'CM31::from_le_bytes':'K053/54 and exact KMX controls pass; full reference/prefix/carrier proof L064. L072 additionally binds S8 values; L073 supplies generic KMX relocation. Still needs an exact native same-allocation/caller occurrence join beyond the bounded16-byte witness. No shorter fixture is promoted.',
'QM31::from_le_bytes':'K055/56 and exact KMX controls pass; L069 full reference/Result/lossless carrier/frame. L072 binds S8 values and L083 proves model caller window bounds. Still needs actual native caller-allocation/borrow and occurrence transport beyond the32-byte witness. Model equality is not itself composed credit.',
'WideExact::from_le_bytes':'K057/58 arbitrary-offset fixed32 window and exact KMX controls pass. L070/L078/L082 now prove complete reference/cohort byte-order and all-length Result; L085 gives the emitted weights.field window/unwrap. Still needs native same-caller backing/borrow/Result transport beyond the64/128-byte witness and general rejection association.',
'M31::inv':'K063/64 source-fission local17-call log and exact erasure+4 controls; K065/66 actual zero panic. L077 now proves all17 legal model calls, canonical replies, extracted return and exact zero assertionFailure. Still needs complete actual native nonzero source-fission/result/ordered-call transport; a local logged clone and token erasure alone are not an adopted whole frozen-function output bridge.',
'CM31::inv':'CM fixed-backend specialization six controls replayed, request for adoption recorded. z(2) DEFERRED; K-2 function-pointer quarantine remains. No Lean theorem may self-adopt this native specialization.',
'CM31::inv_with':'Same deferred CM backend adoption and K-2 quarantine; callback association cannot be replaced by a literal callback or renamed verdict.',
'QM31::inv':'Reaches CM31 inverse/backend; deferred z(2)/K-2 plus full actual native result/trace association remain.',
'QM31::try_inv':'Reaches deferred CM31 inverse; same current normalization and product operands must be bound through native caller. Mathematical domain lemmas cannot discharge K-2.',
'CM31::neg':'Real M31::neg dependency is outside Q; no outside-slice bridge may be developed here. Needs supplied boundary bridge and native caller association.',
'QM31::neg':'Real M31::neg boundary (through CM31::neg) outside Q, plus exact nested call association; no pruning of a typed real dependency.',
'QM31::is_zero':'CM31::is_zero is outside Q. Needs its retained boundary packet and actual native same-value caller association.',
'QM31::square':'Real CM31::square dependency is outside Q. Existing field value/canonical laws do not establish that missing native boundary or whole source caller association.',
'query_loop':'query_values, folds/dots/accumulation arithmetic and root loop native-step bridge remain OPEN. z(1) observer None and getter/opening domains are closed independently. Cannot replace loop proof with a whole-buffer unwind.',
'query_values':'Independent mark/getter/opening child uses are CLOSED; arithmetic folds/dots/accumulation and exact native same-state Result/ordered-effect step remain OPEN. Need an actual one-query native bridge, not accepted-run projections only.',
'four_dots':'Requires four_dots_one whole one-window native packet and loop/caller association. NEI current committed revision supplies neither. Existing loop laws alone cannot create a native step.',
'four_dots_one':'Finisher/new/getter leaves imported and CLOSED; still needs actual one-column source/result/callee-domain bridge and arithmetic caller association. No peer packet currently supplies it.',
'EbyKDot::push':'checked_q/from_wide leaves CLOSED, but current mutable dot state, products/canonical::Dot::push and native one-step log remain OPEN. No whole buffer unwinding.',
'canonical::Dot::push':'Native one-step mutable accumulator/product carry and exact overflow/error/result association missing; no committed NEI closure currently available.',
'QueryGeometry::for_range':'K077/78 proves only empty ranges. Nonempty forward/backward Vec growth, prefix/inversion same-index association and native iteration induction bridge remain OPEN. Gather-prefix L034 and index constructor edge do not prove entire function.',
'accumulate_batched_with_node':'basis/weight getter, row and BatchedWeights::push leaves CLOSED; actual native arbitrary accumulator/width/current-loop iteration and dot/arithmetic/error association remain OPEN.',
'batch_prefix_products':'Needs actual native single forward product/push step paired with Lean same-vector induction. Latest NEI import does not close this member; no field multiplication body may be attempted in Kani.',
'circle_fold_with_inverses':'Needs native fixed-input opaque-product/add/sub step and exact same returned tuple association. Current NEI revision has no accepted closure; generic canonical laws do not supply source refinement.',
'line_fold_with_inverses':'Same missing native product/sub step and same-index inverse/result association, independent of unrelated root blockers. No matching committed NEI closure available.',
'field':'K073/74 proves successful canonical fixed32 windows in128-byte input, K075/76 one malformed panic fixture. Full arbitrary caller backing and all rejected-window panic prefixes are not proved by those tests. Needs complete source/window/Result association; do not narrow to fixture.',
}
def key(f):
 return next((k for k in reasons if f.endswith('::'+k)),None)
rows=[]
for f in q['functions']:
 if f in closed:continue
 k=key(f);assert k,f
 rs=[r['row'] for r in b['rows'] if r['function']==f]
 rows.append(dict(function=f,rows=rs,status='OPEN',obligation=reasons[k]))
open_edges=[]
for e in edges:
 if e['status']=='CLOSED':continue
 k=key(e['caller'])
 open_edges.append(dict(edge=e['edge'],callee_composed=e['callee'] in closed,obligation=reasons[k] if k else 'Unregistered exact same-caller native/Result/state/effect/callee-domain association; no independent callee closure implies this edge.'))
out=dict(schema='NEO-remaining-audit-v1',baseline_sha256=hashlib.sha256((R/'evidence/ledger4-20261102/NEN_LEDGER.json').read_bytes()).hexdigest(),composed=d['total_closed'],q_closed=d['q_closed'],edge_closed=d['edge_closed'],remaining_functions=rows,remaining_edges=open_edges,credit_granted=False)
(E/'NEO_REMAINING.json').write_text(json.dumps(out,indent=1)+'\n')
text='# Remaining Slice Q obligations\n\nFinal frontier audit: root status remains OPEN and no credit is granted here. All80 native runs and10 extraction runs are used. Independent Lean continuation completed throughL086 (86/100 used), including the48-module/98-theorem co-import/axioms audit. The14 unused Lean slots cannot establish the remaining native/owner/boundary facts without new evidence. Each member and edge below records the exact obstacle.\n\n'
for x in rows:text+='## '+x['function']+'\n\n'+', '.join(x['rows'])+': '+x['obligation']+'\n\n'
text+='Every remaining edge is enumerated individually in NEO_REMAINING.json with its caller obligation and whether its callee is already composed. A CLOSED callee alone never establishes the caller domain, state, Result or ordered-effect association.\n'
(E/'NEO_REMAINING.md').write_text(text);print(len(rows),'open functions;',len(open_edges),'open edges')
