#!/usr/bin/env python3
"""NED/NDT checks plus ruling-(y) gates. This never promotes local model facts."""
from pathlib import Path
import argparse, copy, hashlib, json, sys
E=Path(__file__).resolve().parent
R=E.parent.parent
sys.path.insert(0,str(R/'evidence/slice-s-compose-20261029'))
import NED_validate as inherited
BASE_CERTIFICATE=inherited.certificate
read=inherited.read

def ruling_y(c):
    """All three parts must be pinned; booleans alone grant no evidence."""
    try:
        y=c['assume_guarantee']
        assert y['principle']=='C3-BIN ruling (y), 2026-10-29'
        assert y['trust_classification']=='P6/D188 option A reclassification'
        assert y['new_trust_rows']==[]
        caller=y['caller']
        assert caller['exact_arguments'] and caller['prestate_logged']
        assert caller['full_result_unconstrained'] and caller['modifies_unconstrained']
        assert caller['result_final_state_ordered_effects'] and caller['all_domains_established']
        assert caller['control_corrupts'] in {'reply','argument'}
        # Receipts and code are hashed, with independent failing controls.
        for kind in ['positive','negative']:
            rc=json.loads(inherited.artifact(caller[kind]['receipt']))
            assert rc['kind']=='kani' and int(rc['swaps'])==0
            assert rc['limits']=={'memory.high':'6442450944','memory.max':'8589934592','memory.swap.max':'0','pids.max':'64'}
            assert (rc['exit_status']==0)==(kind=='positive')
            assert float(rc['wall_seconds'])>=0 and int(rc['peak_rss_kib'])>0
            assert rc['source_revision']
            log=inherited.artifact(caller[kind]['stdout']).decode()
            if kind=='positive': assert 'VERIFICATION:- SUCCESSFUL' in log
            else:
                assert 'VERIFICATION:- FAILED' in log and caller['control_assertion'] in log
                assert 'timed out' not in log.lower()
            graph=json.loads(inherited.artifact(caller[kind]['graph']))
            assert graph['graph_matches_frozen'] and graph['exact_LPm_graph']
            lock=json.loads(inherited.artifact(caller[kind]['lock']))
            assert lock['unchanged'] and lock['before']==lock['after']
            features=json.loads(inherited.artifact(caller[kind]['features']))
            assert features['features_all_crates']
            source=inherited.artifact(caller[kind]['source']).decode()
            assert 'static mut' not in source and 'UnsafeCell' not in source
            assert 'Cell<' not in source and 'Atomic' not in source
        assert y['children']
        for child in y['children']:
            assert child['bridge_status']=='CLOSED-CONDITIONAL'
            assert child['domain_theorems'] and child['physical_derivation_theorems']
            assert child['modifies_exact'] and child['frame_proved']
            for t in child['domain_theorems']+child['physical_derivation_theorems']:
                assert inherited.theorem(t)
            # The source span of an actual contract is required; a bridge name
            # or a direct native harness without a frame cannot fill this slot.
            source=inherited.artifact(child['contract_source']).decode()
            assert child['contract_statement'] in source
            assert '#[kani::modifies(' in child['contract_statement']
            assert child['proof_for_contract'] and child['matched_control']
            inherited.artifact(child['proof_for_contract'])
            inherited.artifact(child['matched_control'])
        assert y['substitution_theorems']
        assert all(inherited.theorem(t) for t in y['substitution_theorems'])
        return True
    except (AssertionError,KeyError,ValueError,TypeError,OSError):
        return False

def shape_admitted(shape,admission):
    try:
        assert admission.get('admitted') is True
        if shape=='Bool':
            assert admission['basis']=='C3-BIN ruling (t): inherited NCC pure Bool/record interface; no new interface shape used by the payment canonicality predicate'
            return True
        assert shape in {'fixed4','common','tuple'}
        assert set(admission['controls'])=={'native','unimplied','frame','inverted'}
        for name,p in admission['controls'].items():
            rc=json.loads(inherited.artifact(p['receipt']))
            assert rc['kind']=='kani' and int(rc['swaps'])==0 and rc['source_revision']
            assert rc['module']=='pool_v1::payment_relation::NEE_shape::'+{'native':'native_weak','unimplied':'unimplied','frame':'frame_violation','inverted':'inverted_contract'}[name]
            assert (rc['exit_status']==0)==(name=='native')
            assert rc['limits']=={'memory.high':'6442450944','memory.max':'8589934592','memory.swap.max':'0','pids.max':'64'}
            log=inherited.artifact(p['stdout']).decode()
            assert ('VERIFICATION:- SUCCESSFUL' if name=='native' else 'VERIFICATION:- FAILED') in log
            assert 'timed out' not in log.lower()
            if name=='inverted': assert 'Failed Checks: |r| !same(' in log
            if name=='frame': assert 'is assignable' in log
            if name=='unimplied': assert 'in pool_v1::payment_relation::NEE_shape::unimplied' in log
            source=inherited.artifact(p['source']).decode()
            assert rc['source_hashes']['NEE_native_contracts.patch']==p['source']['sha256']
            assert '+type A='+admission['return_type']+';' in source
            assert 'static mut' not in source and 'UnsafeCell' not in source
            assert 'Cell<' not in source and 'Atomic' not in source
            graph=json.loads(inherited.artifact(p['graph']))
            assert graph['graph_matches_frozen'] and graph['exact_LPm_graph']
            lock=json.loads(inherited.artifact(p['lock']))
            assert lock['unchanged'] and lock['before']==lock['after']
            assert json.loads(inherited.artifact(p['features']))['features_all_crates']
        return True
    except (AssertionError,KeyError,ValueError,TypeError,OSError):return False

def direct_contract(c,expected,ledger):
    try:
        d=c['direct_contract']
        assert d['method']=='NCO actual frozen function contract'
        assert d['trust_classification']=='P6/D188 option A reclassification'
        assert d['actual_body_unchanged'] and d['full_result'] and d['empty_modifies']
        assert d['all_inputs_domain'] and d['no_stub_verified']
        assert d['real_internal_calls']==[]
        assert isinstance(d['alternative_targets_resolved'],list)
        f=d['function'];binding=read(E/'NEE_MODEL_BINDINGS.json')[f]
        assert d['proof_target']==binding['proof_target']
        admission=read(E/'NEE_SHAPE_ADMISSIONS.json').get(binding['shape'],{})
        assert shape_admitted(binding['shape'],admission),('unadmitted contract shape',binding['shape'])
        assert [t['name'] for t in d['domain_and_model_theorems']]==binding['model_theorems']
        assert d['positive']['receipt']['sha256']==binding['positive_receipt_sha256']
        assert d['negative']['receipt']['sha256']==binding['negative_receipt_sha256']
        rs=[r for r in ledger['rows'] if r['function']==f];assert rs
        assert expected==f or expected.startswith(f+'::')
        assert set(d['alternative_targets_resolved'])=={g for r in rs for g in r['canonical_callees']}
        patch=inherited.artifact(d['contract_source']).decode()
        assert d['modifies_statement'] in patch and '#[cfg_attr(kani,kani::modifies())]' in patch
        assert d['ensures_statement'] in patch
        for kind in ['positive','negative']:
            p=d[kind];rc=json.loads(inherited.artifact(p['receipt']))
            assert rc['kind']=='kani' and (rc['exit_status']==0)==(kind=='positive')
            assert int(rc['swaps'])==0 and rc['source_revision'] and int(rc['peak_rss_kib'])>0
            assert rc['limits']=={'memory.high':'6442450944','memory.max':'8589934592','memory.swap.max':'0','pids.max':'64'}
            log=inherited.artifact(p['stdout']).decode()
            assert ('VERIFICATION:- SUCCESSFUL' if kind=='positive' else 'VERIFICATION:- FAILED') in log
            if kind=='negative':assert 'Failed Checks:' in log and 'CBMC timed out' not in log
            graph=json.loads(inherited.artifact(p['graph']))
            assert graph['graph_matches_frozen'] and graph['exact_LPm_graph']
            lock=json.loads(inherited.artifact(p['lock']));assert lock['unchanged'] and lock['before']==lock['after']
            features=json.loads(inherited.artifact(p['features']));assert features['features_all_crates']
            native=json.loads(inherited.artifact(p['config']))
            assert native['copy_patch_sha256']=='bcdf749b78eb6143789500d98d64ec3d407b8a17a6d1290c70c822473e8e9a67'
            assert native['env']['CARGO_NET_OFFLINE']=='true' and native['env']['CARGO_PROFILE_DEV_OPT_LEVEL']=='3'
            assert rc['source_hashes']['NEE_oracle.patch']==p['oracle_patch']['sha256']
            inherited.artifact(p['oracle_patch'])
            assert rc['source_hashes'][p['harness_key']]==p['harness']['sha256']
            assert rc['source_hashes']['NEE_native_contracts.patch']==p['contract_source']['sha256']
            inherited.artifact(p['contract_source'])
            source_check=json.loads(inherited.artifact(p['source_check']));assert source_check['errors']==[]
            source=inherited.artifact(p['harness']).decode()
            assert d['proof_target'] in source and '#[kani::proof_for_contract(' in source
        assert all(inherited.theorem(t) for t in d['domain_and_model_theorems'])
        assert d['domain_and_model_theorems']
        return True
    except (AssertionError,KeyError,ValueError,TypeError,OSError):return False

def certificate(c,expected,ledger,reviewed):
    if not BASE_CERTIFICATE(c,expected,ledger,reviewed): return False
    # Alternative resolution does not invoke a child. Every execution-bearing
    # certificate additionally needs the three assume-guarantee parts.
    return c['kind']=='alternative-resolution' or (direct_contract(c,expected,ledger) if 'direct_contract' in c else ruling_y(c))

def inventory_edge_overlay(base,out,packet,reviewed):
    # The slice JSON omits self edges while NDT retains them as actual open
    # obligations. A separate input field adds certificates for precisely those
    # existing obligations. Never alter the original spec or its assertions.
    spec=read(R/'docs/research/100bit-spend-path-20261013/design/VERTICAL-SLICES-20261029.json')['slices']['S']
    allowed={r['function']+' -> '+r['function'] for r in base['rows'] if r['function'] in spec['functions'] for o in r['caller_domain_obligations'] if o.get('callee')==r['function']}
    extra=packet.get('inventory_edges',{})
    assert set(extra)<=allowed,'non-inventory supplemental edge'
    for edge,c in extra.items():
        if c.get('kind')!='alternative-resolution' or not certificate(c,edge,base,reviewed):continue
        for row in out['rows']:
            for ob in row['caller_domain_obligations']:
                if ob.get('caller',row['function'])+' -> '+ob.get('callee','<unresolved>')==edge:
                    ob.update(status='CLOSED',discharged_by=c['id'])
    edges=dict(packet['edges'],**extra)
    byfunction={}
    for row in out['rows']:byfunction.setdefault(row['function'],[]).append(row)
    changed=True
    while changed:
        changed=False
        for f in spec['functions']:
            c=packet['roots'].get(f) or packet['members'].get(f)
            if not certificate(c,f,base,reviewed):continue
            for row in byfunction[f]:
                if row['composed_status']=='CLOSED':continue
                if row['bridge_status']!='CLOSED-CONDITIONAL' or not row['selected_claims'] or row['open_transitive_dependencies']:continue
                if any(not h['discharged_by'] for h in row['named_hypotheses']):continue
                if any(o['status']!='CLOSED' or not o['discharged_by'] for o in row['caller_domain_obligations']):continue
                deps=[g for g in row['canonical_callees'] if not (edges.get(f+' -> '+g,{}).get('kind')=='alternative-resolution' and certificate(edges.get(f+' -> '+g),f+' -> '+g,base,reviewed))]
                if any(any(r['composed_status']!='CLOSED' for r in byfunction[g]) for g in deps):continue
                row.update(composed_status='CLOSED',composed_reason='NEE checked framed leaf and inventory-edge certificates '+c['id']);changed=True
    for row,old in zip(out['rows'],base['rows']):
        assert {k:v for k,v in row.items() if k not in {'composed_status','composed_reason','caller_domain_obligations','named_hypotheses'}}=={k:v for k,v in old.items() if k not in {'composed_status','composed_reason','caller_domain_obligations','named_hypotheses'}}
        for got,previous in zip(row['caller_domain_obligations'],old['caller_domain_obligations']):
            assert dict(got,status=previous['status'],discharged_by=previous['discharged_by'])==previous
        if row['composed_status']=='CLOSED':
            assert all(h['discharged_by'] for h in row['named_hypotheses'])
            assert all(o['status']=='CLOSED' and o['discharged_by'] for o in row['caller_domain_obligations'])
            assert row['bridge_status']=='CLOSED-CONDITIONAL' and row['selected_claims'] and not row['open_transitive_dependencies']
    out['NEE_inventory_edge_overlay']={'allowed_existing_self_edges':sorted(allowed),'certified':sorted(e for e,c in extra.items() if certificate(c,e,base,reviewed))}
    return out

def compose(base,packet,reviewed):
    previous=inherited.certificate
    try:
        inherited.certificate=certificate
        out=inherited.compose(base,packet,reviewed)
        return inventory_edge_overlay(base,out,packet,reviewed)
    finally:
        inherited.certificate=previous

def main():
    ap=argparse.ArgumentParser();ap.add_argument('--packet',type=Path,default=E/'NEE_LEDGER_DELTA.json');ap.add_argument('--write',type=Path);a=ap.parse_args()
    base=read(R/'evidence/native-ledger3-20261029/NDT_LEDGER.json')
    out=compose(base,read(a.packet),read(E/'NEE_REVIEWED_CERTIFICATES.json'))
    if a.write:a.write.write_text(json.dumps(out,indent=1)+'\n')
    spec=read(R/'docs/research/100bit-spend-path-20261013/design/VERTICAL-SLICES-20261029.json')['slices']['S']
    print(json.dumps({'slice_closed':[r['row'] for r in out['rows'] if r['function'] in spec['functions'] and r['composed_status']=='CLOSED'], 'roots':{f:[r['composed_status'] for r in out['rows'] if r['function']==f] for f in spec['roots']},'inherited_checks_preserved':True},indent=1))
if __name__=='__main__':main()
