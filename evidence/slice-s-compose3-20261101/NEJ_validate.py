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
BASE_CERTIFICATE=predecessor.certificate
read=predecessor.read

def call_domain(c,expected,ledger):
    try:
        d=c['call_domain_certificate']
        assert c['kind'] in {'call-domain','hypothesis-discharge','root-composition','external-domain','alternative-resolution'}
        assert d['subject']==expected
        assert d['frozen_revision']==ledger['frozen_revision']
        assert d['native_association_kind'] in {'ruling-y','native-contract'}
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
    if not BASE_CERTIFICATE(c,expected,ledger,reviewed):return False
    # Imported NEE certificates remain unchanged, with their original hashes.
    if not c['id'].startswith('NEJ_'):return True
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
