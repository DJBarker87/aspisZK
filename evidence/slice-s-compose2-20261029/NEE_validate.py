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
            inherited.artifact(caller[kind]['source'])
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

def certificate(c,expected,ledger,reviewed):
    if not BASE_CERTIFICATE(c,expected,ledger,reviewed): return False
    # Alternative resolution does not invoke a child. Every execution-bearing
    # certificate additionally needs the three assume-guarantee parts.
    return c['kind']=='alternative-resolution' or ruling_y(c)

def compose(base,packet,reviewed):
    previous=inherited.certificate
    try:
        inherited.certificate=certificate
        return inherited.compose(base,packet,reviewed)
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
