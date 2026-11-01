#!/usr/bin/env python3
"""Strict additive NDT -> NED -> NEE -> NEJ certificate validation.

NEJ acceptance requires every inherited gate AND explicit call-domain bindings.
A model frame, isolated native window or unreviewed candidate cannot close a row.
"""
from pathlib import Path
import argparse,copy,hashlib,json,sys
E=Path(__file__).resolve().parent;R=E.parent.parent
sys.path.insert(0,str(R/'evidence/slice-s-compose2-20261029'))
import NEE_validate as predecessor
import NEJ_loop_checks
BASE_CERTIFICATE=predecessor.certificate
read=predecessor.read
inherited=predecessor.inherited

def direct_contract(c,expected,ledger):
    try:
        d=c['direct_contract']
        assert d['method']=='NCO actual frozen function contract'
        assert d['trust_classification']=='P6/D188 option A reclassification'
        assert d['actual_body_unchanged'] and d['full_result'] and d['empty_modifies']
        assert d['all_inputs_domain'] and d['no_stub_verified']
        assert d['real_internal_calls']==[]
        assert isinstance(d['alternative_targets_resolved'],list)
        f=d['function'];binding=read(E/'NEJ_MODEL_BINDINGS.json')[f]
        original=read(predecessor.E/'NEE_MODEL_BINDINGS.json')[f]
        assert {k:v for k,v in binding.items() if k not in {'positive_receipt_sha256','negative_receipt_sha256'}}=={k:v for k,v in original.items() if k not in {'positive_receipt_sha256','negative_receipt_sha256'}}
        assert d['proof_target']==binding['proof_target']
        admission=read(predecessor.E/'NEE_SHAPE_ADMISSIONS.json').get(binding['shape'],{})
        assert predecessor.shape_admitted(binding['shape'],admission),('unadmitted contract shape',binding['shape'])
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
            assert rc['source_hashes']['NEJ_oracle.patch']==p['oracle_patch']['sha256']
            inherited.artifact(p['oracle_patch'])
            assert rc['source_hashes'][p['harness_key']]==p['harness']['sha256']
            assert rc['source_hashes']['NEJ_native_contracts.patch']==p['contract_source']['sha256']
            inherited.artifact(p['contract_source'])
            source_check=json.loads(inherited.artifact(p['source_check']));assert source_check['errors']==[]
            source=inherited.artifact(p['harness']).decode()
            assert 'static mut' not in source and 'UnsafeCell' not in source
            assert 'Cell<' not in source and 'Atomic' not in source
            assert d['proof_target'] in source and '#[kani::proof_for_contract(' in source
        assert all(inherited.theorem(t) for t in d['domain_and_model_theorems'])
        assert d['domain_and_model_theorems']
        return True
    except (AssertionError,KeyError,ValueError,TypeError,OSError):return False


def call_domain(c,expected,ledger):
    try:
        d=c['call_domain_certificate']
        assert c['kind'] in {'call-domain','hypothesis-discharge','root-composition','external-domain','alternative-resolution'}
        assert d['subject']==expected
        assert d['frozen_revision']==ledger['frozen_revision']
        assert d['native_association_kind'] in {'ruling-y','native-contract','native-loop'}
        assert d['domain_theorems'] and d['physical_theorems']
        assert all(predecessor.inherited.theorem(t) for t in d['domain_theorems']+d['physical_theorems'])
        assert d['selected_callee_claims']
        assert d['inner_hypotheses_remaining']==[]
        assert d['exact_callsite'] and d['canonical_carrier']
        assert d['same_arguments'] and d['same_prestate'] and d['same_result'] and d['same_ordered_effects']
        assert d['trust_classification']=='P6/D188 option A reclassification'
        assert d['new_trust_rows']==[]
        assert d['native_frame_complete'] is True
        # Bind each certificate to the actual inventory obligation; conservative
        # alternatives cannot disappear through an unselected claim label.
        if c['kind']=='call-domain':
            caller,callee=expected.split(' -> ')
            obs=[o for row in ledger['rows'] if row['function']==caller for o in row['caller_domain_obligations'] if o.get('callee')==callee]
            assert obs and set(d['selected_callee_claims'])==set(x for o in obs for x in o['callee_claims'])
            assert set(d['inner_names_discharged'])==set(x for o in obs for x in o['required_named_hypotheses'])
        return True
    except (AssertionError,KeyError,ValueError,TypeError,OSError):return False

def certificate(c,expected,ledger,reviewed):
    if not c or not c.get('id','').startswith('NEJ_'):
        return BASE_CERTIFICATE(c,expected,ledger,reviewed)
    # Same NDT/NED review, statement, receipt and hypothesis gates. The copied
    # native gate differs only in names of THIS lane's hashed patch artifacts.
    # All existing NEE certificates still run the original checker unchanged.
    if predecessor.suspended_reference(c):return False
    if not predecessor.BASE_CERTIFICATE(c,expected,ledger,reviewed):return False
    if c['kind']!='alternative-resolution':
        if 'loop_composition' in c:
            if not NEJ_loop_checks.validate(c,expected,ledger,sys.modules[__name__]):return False
        elif not (direct_contract(c,expected,ledger) if 'direct_contract' in c else predecessor.ruling_y(c)):return False
    return call_domain(c,expected,ledger)

def compose(base,packet,reviewed):
    previous=predecessor.certificate
    try:
        predecessor.certificate=certificate
        return predecessor.compose(base,packet,reviewed)
    finally:predecessor.certificate=previous

def summary(out):
    s=read(R/'docs/research/100bit-spend-path-20261013/design/VERTICAL-SLICES-20261029.json')['slices']['S']
    return dict(slice_closed=[r['row'] for r in out['rows'] if r['function'] in s['functions'] and r['composed_status']=='CLOSED'],roots={f:[r['composed_status'] for r in out['rows'] if r['function']==f] for f in s['roots']},inherited_checks_preserved=True)

def main():
    p=argparse.ArgumentParser();p.add_argument('--packet',type=Path,default=E/'NEJ_LEDGER_DELTA.json');p.add_argument('--write',type=Path);a=p.parse_args()
    out=compose(read(R/'evidence/native-ledger3-20261029/NDT_LEDGER.json'),read(a.packet),read(E/'NEJ_REVIEWED_CERTIFICATES.json'))
    if a.write:a.write.write_text(json.dumps(out,indent=1)+'\n')
    print(json.dumps(summary(out),indent=1))
if __name__=='__main__':main()
