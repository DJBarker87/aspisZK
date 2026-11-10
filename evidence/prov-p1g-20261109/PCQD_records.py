#!/usr/bin/env python3
"""Write PCQD_COVERAGE / NO_FROZEN_COUNTERPART / FAILURES / RECEIPT_SUMMARY / TOOLS from receipts and emissions."""
import json,re,lzma,subprocess,sys
from pathlib import Path
sys.dont_write_bytecode=True
E=Path(__file__).resolve().parent;EV=E.parent
J=lambda p:json.loads(Path(p).read_text())
subprocess.run([sys.executable,'-B',str(E/'PCQD_index.py'),str(E/'PCQD_INDEX.json')],check=True,capture_output=True)
idx=J(E/'PCQD_INDEX.json')
need=J(EV/'prov-p3b-20261109/PCVB_NEED_EXTRACTION.json')['entries']
specs={s['spec_id']:s for s in J(E/'PCQD_extract_specs.json')['specs']}
# ---- runs
runs={}
for l in (E/'PCQD_ATTEMPTS.jsonl').read_text().splitlines():
    x=json.loads(l)
    if x.get('event')=='result':
        a=x['attempt'];sp=J(E/(a+'_spec.json'));pp=E/(a+'_emitted')/(a+'_PINS.json');pn=J(pp) if pp.exists() else dict(tools={},frozen_revision=None)
        rc=J(E/a/'receipt.json')
        err=None
        if x['exit_status']!=0:
            try:log=lzma.decompress((E/a/'stdout.log.xz').read_bytes()).decode(errors='replace')
            except Exception:log=''
            m=re.search(r'(Name clash detected[^\n]*|Nested-loop returns require exactly one Option language item|Returns inside of nested loops[^\n]*|Markers remain after collapsing[^\n]*|Not_found|Internal error, please file an issue[^"]*?Source: \'[^\']*\', lines [0-9:\-]*|Unreachable[^"]*?Source: \'[^\']*\', lines [0-9:\-]*|Type error after transformations[^\n]*|Mismatched trait clause)',log.replace('\\n','\n'),re.S)
            err=(m.group(1) if m else (('timeout 180 s; cgroup peak %s bytes (> MemoryHigh 3 GiB: memory growth / throttle)'%rc.get('cgroup_memory_peak_bytes') if int(rc.get('cgroup_memory_peak_bytes') or 0)>3221225472 else 'timeout 180 s; cgroup peak %s bytes (< MemoryHigh): cold cargo build or slow Aeneas, not memory'%rc.get('cgroup_memory_peak_bytes')) if x['exit_status']==124 else 'charon/cargo failure exit %s'%x['exit_status']))[:300].replace('\n',' ')
        runs[a]=dict(run=a,spec=sp['spec_id'],tool=sp.get('aeneas_tool'),exit=x['exit_status'],wall_seconds=round(rc['wall_seconds'],1),peak_rss_kib=rc['peak_rss_kib'],cgroup_peak_bytes=rc.get('cgroup_memory_peak_bytes'),swaps=rc['swaps'],
          overflow_checks='ON',features=sp['configuration']['features'],roots=sp['configuration']['start_from'],opaque=sp['configuration']['opaque'],include=sp['configuration']['include'],
          rustflags_extra=(sp.get('extra_env') or {}).get('RUSTFLAGS'),frozen_revision=pn.get('frozen_revision'),aeneas_sha256=[v for k,v in pn['tools'].items() if k.startswith('aeneas')],namespace=sp['configuration']['namespace'],error=err)
json.dump(dict(schema='PCQD_RECEIPT_SUMMARY/1',runs=list(runs.values())),open(E/'PCQD_RECEIPT_SUMMARY.json','w'),indent=1)
fails=[r for r in runs.values() if r['exit']!=0]
json.dump(dict(schema='PCQD_FAILURES/1',target_established=False,failures=fails),open(E/'PCQD_FAILURES.json','w'),indent=1)
# ---- coverage
ALIAS={'AspisR1.NGN_Emitted.folds':'transport.Variant.folds','AspisR1.NGN_Emitted.prepared':'verifier.Prepared.new','AspisR1.NGN_Emitted.variantEq':'transport.Variant.Insts.CoreCmpPartialEqVariant.eq',
 'AspisR1.Port5Q2_ReaderValidate.validate':'verifier.validate_checkpoint_queries','AspisR1.Port5Q2_ReaderValidate.validate_loop':'verifier.validate_checkpoint_queries_loop',
 'AspisR1.Port5Q2_ReaderWeights.weights':'verifier.read_checkpoint_weights','AspisR1.Port5Q2_ReaderWeights.weights_loop':'verifier.read_checkpoint_weights_loop',
 'FLAGGED_SYMBOL aspis_r1_cost_probe::verifier::{aspis_r1_cost_probe::verifier::BatchedWeights}::new':'verifier.BatchedWeights.new'}
NOFROZEN={'AspisR1DecodeKFullV10.r1_wire.ValidatedRecord.decode_k_value':'no function decode_k_value anywhere in frozen 4bb3b3f crates/ or programs/ (gate-only helper)',
 'AspisR72Sampler.field.r24_canonical_mul.closure':'r24_canonical_mul / r24_guarded_qm.rs absent from frozen 4bb3b3f (P3b: eight-limb wrapping algorithm exists only in the gate)',
 'NJT_ClaimsRef.r1_semantic.NJT_claims_ref':'NJT_claims_ref is a reference function of the claims-queryscan candidate (NJT_claims_ref.rs.txt); absent from frozen 4bb3b3f; the nearest frozen function is r1_semantic::claims (see AspisR1ClaimsUnrolledParent)',
 'AspisR1ClaimsUnrolledParent.candidate_claims.claims':'frozen 4bb3b3f has no candidate_claims.rs/module; the frozen function with this role is r1_semantic::claims (extraction attempt D05, outcome in its status)'}
fresh={};prior={}
for d,v in idx.items():
    if v['superseded_by']:continue
    tgt=fresh if v['run'].startswith('PCQD_') else prior
    for n,k in v['defs'].items():tgt.setdefault(n,[]).append(dict(run=v['run'],tool=v['tool'],kind=k,dir=d))
def find(tbl,tail):
    out=[]
    for n,h in tbl.items():
        nt=n.split('.')
        if nt==tail or (len(tail)>=2 and nt[-len(tail):]==tail):out+=[dict(name=n,**x) for x in h]
    return out
cov=[]
for e in need:
    g=e['gate_definition']
    if g in ALIAS:tail=ALIAS[g].split('.')
    else:tail=g.split('.')[2:] if g.startswith('AspisR1.') else g.split('.')[1:]
    if g.startswith('AspisR1.') or g.startswith('AspisR1CurrentCaller'):pass
    f=find(fresh,tail);p=find(prior,tail)
    if g in NOFROZEN:st='NO_FROZEN_COUNTERPART';ev=NOFROZEN[g]
    elif f:st='FRESH_PRESENT_PCQD';ev=f[:3]
    elif p:st='ALREADY_COVERED';ev=p[:3]
    else:st='NOT_OBTAINED';ev=None
    cov.append(dict(module=e['module'],gate_definition=g,status=st,frozen_name_tail='.'.join(tail),evidence=ev,candidate_frozen_files=e['candidate_frozen_files'],required_configuration=e['required_configuration']))
summ={}
for c in cov:summ[c['status']]=summ.get(c['status'],0)+1
r0=find(fresh,'r0.transport.order'.split('.'))+find(prior,'r0.transport.order'.split('.'))
prio=dict(item='r0.transport.order (FIo_Native, last unexamined SEMANTIC item)',
 fresh_extraction_exists=bool(r0),
 emissions=[dict(run=x['run'],tool=x['tool'],name=x['name'],dir=x['dir'],overflow_checks='ON',features='r0',frozen_revision='4bb3b3f51e16b4525f1d10336e2b0bcbbd775387') for x in r0 if x['name']=='r0.transport.order'],
 note='P1d PCQE_E001 (original Aeneas 959659a6, overflow-checks ON, features r0, start-from crate::r0::transport::order + ok_or) emits order and order_loop0, order_loop0.body, order_loop0_loop0, order_loop0_loop0.body. PCQD_E006 tried the extended Aeneas once: failed (Not_found), so no extended emission exists. Name-level presence is not equality; no comparison with the gate was done in P1g.')
cfg={}
json.dump(dict(schema='PCQD_COVERAGE/1',target_established=False,note='Name-level presence only (def-kind names in Types.lean/Funs.lean); equality is P2/P3. Tool and configuration are per evidence run.',summary=summ,priority_r0_transport_order=prio,entries=cov),open(E/'PCQD_COVERAGE.json','w'),indent=1)
json.dump(dict(schema='PCQD_NO_FROZEN_COUNTERPART/1',items=[dict(gate_definition=k,reason=v) for k,v in NOFROZEN.items()]),open(E/'PCQD_NO_FROZEN_COUNTERPART.json','w'),indent=1)
print(summ,len(runs),len(fails))
