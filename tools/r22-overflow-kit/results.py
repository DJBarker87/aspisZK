#!/usr/bin/env python3
"""Per-site table. Local range results never imply accepted-run composition."""
import collections,csv,hashlib,json,re,sys
from pathlib import Path
sys.path.insert(0,str(Path(__file__).resolve().parent))
from inventory import ROOT,OUT,blob,walk,owner,text
from prepare import P

def attributes(n,b):
    attrs=[]
    while n:
        if n.type in ('mod_item','function_item','impl_item','const_item','static_item'):
            p=n.prev_named_sibling
            while p and p.type in ('attribute_item','line_comment','block_comment'):
                if p.type=='attribute_item':attrs.append(text(p,b))
                p=p.prev_named_sibling
        n=n.parent
    return attrs

def make():
    x=json.loads((OUT/'operation-census.json').read_text());meta={};fnconst=set()
    for source in x['sources']:
        path=source['path'];b=blob(path);tree=P.parse(b)
        for n in walk(tree.root_node):
            if n.type in ('function_item','const_item','static_item'):
                fnconst.add((path,owner(n,b),'constant' if n.type in ('const_item','static_item') else 'function'))
            if n.type in ('binary_expression','compound_assignment_expr','index_expression','type_cast_expression','call_expression','unary_expression','for_expression'):
                meta[(path,n.start_point.row+1,n.start_point.column+1,n.type)]=attributes(n,b)
    constants={(p,o) for p,o,k in fnconst if k=='constant'}
    rows=[]
    for r in x['operations']:
        p,o,k=r['path'],r['owner'],r['kind'];q=' '.join(meta.get((p,r['line'],r['column'],{'operator':'binary_expression','index':'index_expression','cast':'type_cast_expression','integer_method':'call_expression','arithmetic_call':'call_expression','unary_operator':'unary_expression','iteration_boundary':'for_expression'}[k]),[]))
        if k=='operator' and not q:q=' '.join(meta.get((p,r['line'],r['column'],'compound_assignment_expr'),[]))
        status='OPEN';method='none';condition='typed receiver/range and default-cone membership need review; no safety claim'
        if re.search(r'#\[cfg\(test\)\]',q) or re.search(r'#\[cfg\(feature\s*=\s*"prover"\)\]',q):
            status='CFG_EXCLUDED';method='explicit ancestor cfg';condition=q
        elif k=='iteration_boundary':
            status='ITERATOR_BOUNDARY';method='implicit for iterator counter/step';condition='standard iterator contracts and source loop progress required; body sites indexed separately'
        elif k=='cast':
            status='TOTAL_CAST_RULE';method='Rust as / Aeneas total cast semantics';condition='cast itself only; later index/arithmetic use is separate; translation trust P6 retained'
        elif (p,o) in constants:
            status='CONST_EVAL_BOUNDARY';method='Rust const evaluation';condition='cfg/instantiation not resolved; no dynamic arithmetic claim'
        elif k=='integer_method' and any('.'+name in (r['operator'] or '') for name in ['checked_','wrapping_','saturating_','overflowing_']):
            status='PRIMITIVE_METHOD_RULE';method='Rust primitive integer method is total';condition='requires primitive receiver/translation correspondence; wrapper/caller and nested operands are separate sites'
        if status not in ['CFG_EXCLUDED','CONST_EVAL_BOUNDARY'] and p.endswith('/fast_pairing.rs'):
            if o in ['canonical::reduce','canonical::add','canonical::pair','canonical::reduce_pair','canonical::Q::add','canonical::Q::sub','canonical::Q::half','canonical::Q::half_pow']:
                status='LOCAL_PROVED';method='Kani 17/03/04/05/06; copied bodies + explicit wrapping assertions';condition='reduce: any u64; other methods: canonical Q/limbs <P; reduce_pair is called on packed canonical sum/offset difference, NOT arbitrary u64'
            elif o in ['canonical::Q::raw','canonical::Q::mul'] or o.startswith(('canonical::Q::raw::','canonical::Q::mul::')):
                status='LOCAL_RANGE_PROVED';method='Kani 07-12 + existing R22FastPairingRawRanges.raw_ranges; checked expression correspondence';condition='all input limbs <P; each widened product <=(P-1)^2; partials <=3P; not a whole Q::mul caller theorem'
            elif o in ['canonical::Dot::push','canonical::Q::dot','EbyKDot::push','EbyEDot::push']:
                status='LOCAL_STEP_PROVED';method='Kani 13; R22OverflowWorkerControl';condition='dot prior prefix sum/count and canonical inputs; Q::dot N<=4; source caller invariant propagation remains'
        if status not in ['CFG_EXCLUDED','CONST_EVAL_BOUNDARY'] and p.endswith('/compact.rs') and o=='slot_offset':
            status='LOCAL_PROVED';method='Kani 23 exact frozen body';condition='0<=slot<=6; numeric constant layout copied exactly'
        if status not in ['CFG_EXCLUDED','CONST_EVAL_BOUNDARY'] and p.endswith('/candidate.rs'):
            if o in ['opening','slot']:
                status='LOCAL_PROVED';method='Kani 23/24 exact frozen bodies; R22Stage2OpeningTotal';condition='opening i<22; slot s<6; proof length57607; buffer contents irrelevant to these expressions'
            elif o=='batch_keys':
                status='LOCAL_PROVED';method='Kani 30 exact frozen body';condition='lo<=22, n<=16, lo+n<=22, all query words <2^18; all tree usize values'
        if status not in ['CFG_EXCLUDED','CONST_EVAL_BOUNDARY'] and p.endswith('/multiproof.rs'):
            if o in ['sort_dedup','node_count']:
                status='LOCAL_BODY_STEPS';method='Kani 18/21/29/32; R22OverflowWorkerControl';condition='live sorted prefix for node_count; w<=i<n<=16, nonempty group <=arity width and count/cursor budgets; full concrete loop propagation remains'
        if status not in ['CFG_EXCLUDED','CONST_EVAL_BOUNDARY'] and p.endswith('/verifier.rs') and o in ['update_residue_row','residue_limb_at','power_limb_at']:
            status='LOCAL_STEP_PROVED';method='Kani 36 copied frozen row body with independent bounded products';condition='prior lane <2^34+phase*(P-1)^2, phase<4, canonical power/basis; flush iff phase=3; shared caller terms/cadence not proved'
        if status not in ['CFG_EXCLUDED','CONST_EVAL_BOUNDARY'] and p.endswith('/verifier.rs') and o=="Reader<'a>::raw":
            status='LOCAL_PROVED';method='Kani 33/34/35 exact raw body; existing R22Stage2ReaderTotal';condition='N=4/16/32, cursor+N<=length<=4880; Kani uses zero contents, length/cursor arbitrary; data-independence is a source range argument'
        rows.append(dict(site=r['id'],owner=o,kind=k,result=status,proof_method=method,conditions=condition))
    return rows

def write():
    rows=make();dest=OUT/'operation-results.tsv'
    with dest.open('w') as f:
        w=csv.DictWriter(f,fieldnames=list(rows[0]),delimiter='\t');w.writeheader();w.writerows(rows)
    groups=collections.defaultdict(list)
    for r in rows:
        if r['result']=='OPEN':groups[(r['site'].rsplit(':',3)[0],r['owner'])].append(r['site'])
    with (OUT/'remaining-functions.tsv').open('w') as f:
        w=csv.writer(f,delimiter='\t');w.writerow(['frozen_path','owner','open_sites','exact_site_ids'])
        for (p,o),sites in sorted(groups.items()):w.writerow([p,o,len(sites),' '.join(sites)])
    summary=dict(site_count=len(rows),result_counts=dict(collections.Counter(r['result'] for r in rows)),open_function_groups=len(groups),meaning='OPEN counts a lexical superset including inactive/prover/legacy and overloaded operations; not the number of reachable R22 failures. LOCAL results have explicit range premises and do not close R22.',table_sha256=hashlib.sha256(dest.read_bytes()).hexdigest())
    (OUT/'operation-results-summary.json').write_text(json.dumps(summary,indent=2)+'\n');print(json.dumps(summary))
if __name__=='__main__':write()
