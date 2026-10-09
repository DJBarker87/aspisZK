#!/usr/bin/env python3
"""Focused source/olean/axiom audit and explicitly incomplete recovery ledger."""
import contextlib
import io
import json
from pathlib import Path
import re
import sys

import audit_soundness_proofs as evidence
from audit_causal_rows import checked_leaf
import helper_recovery_caps

BASE = '503332fbe747db381fc8ee67c4bbdd3631ec97cf'
LEAVES = [
    ('DecodedIndex32', 'decoded-index32-v*.log'),
    ('SelectedMembershipDecode', 'selected-membership-decode-v*.log'),
    ('CanonicalCollect', 'canonical-collect-v*.log'),
    ('CanonicalRelationInput', 'canonical-relation-input-v*.log'),
    ('HelperSupportTransfer', 'helper-support-transfer-v*.log'),
    ('QuotientHelperShift', 'quotient-helper-shift-v*.log'),
]


def proofs():
    evidence.BASE = BASE
    leaves = [checked_leaf(*leaf) for leaf in LEAVES]
    for leaf in leaves:
        source = (evidence.EX / leaf['target']).read_text()
        assert not re.search(r'^\s*(axiom|sorry|admit)\b|\bby\s+(sorry|admit)\b', source, re.M)
        log = (evidence.ROOT / leaf['log']).read_text()
        assert 'LEAN_EXIT=0' in log
        paths, runners = {}, []
        for expected, raw in re.findall(r'^([a-f0-9]{64})  (/[^\n]+)$', log, re.M):
            path = Path(raw)
            if path.suffix == '.sh':
                runners.append({'path': raw, 'logged_sha256': expected,
                                'current_sha256': evidence.sha(path)})
                continue
            assert path.exists() and evidence.sha(path) == expected, (raw, expected)
            assert raw not in paths or paths[raw] == expected, ('changed during run', raw)
            paths[raw] = expected
        leaf['current_logged_source_cache_hashes_verified'] = len(paths)
        leaf['runner_versions'] = runners
    return leaves


def result():
    arithmetic = io.StringIO()
    with contextlib.redirect_stdout(arithmetic):
        helper_recovery_caps.main()
    body = 697*16 + 52 + 24 + 22*621 + 2*296*26
    assert body == 40282
    return {
        'base_revision': BASE,
        'borrowed_formal_revision': '26a9cd4718aae9f9de7ef1c3394fb74a229085d5',
        'environment': 'Lean4.32.0 / Mathlib81a5d257; serialized cached leaf checks; -M7000 and7GiB aggregate child RSS guard',
        'leaves': proofs(),
        'arithmetic_controls': json.loads(arithmetic.getvalue()),
        'deterministic_endpoints': {
            'membership': 'same canonical raw semantic table and explicit selected residuals derive literal20-bit UInt32 index, all24 directions/siblings, input-pair selection,20+3 path reconstruction and independently supplied public-root binding; modeled hash/gates, not actual Rust/context authentication',
            'parser': 'length/frontier guard plus exact LE field/list collection derives all697 decodes, literal417/441 response/final offsets and compact omitted-c4 boundary; not full Wire/Merkle/UInt8/Vec refinement',
            'support': 'actual image-valid quotient matching>=26095 and earlyC1=some p construct>=9558 retained full-domain helper fibres, hence>=38232 symbols; no acceptance-to-candidate premise discharged',
            'shift': 'literal zero received word and pre-gamma false lane-zero OOD claims produce -1/L; its gamma^-26 normalized value cannot equal any fixed quadratic on more than28 nonzero gammas at a nonpole; not acceptance or a payment forgery',
        },
        'event_accounting': [
            {'class': 'actual source/authentication/replay mismatch, abort/fuel, missing responses or changed challenges',
             'bound': None, 'status': 'coupling to specified extractor still required'},
            {'class': 'checked witness returned within declared resources',
             'extraction_failure_contribution': '0 by definition; radius/provider labels do not override it'},
            {'class': 'earlyC1=some; supported final distance<=15334; wrong ordinary/OOD C1 claim to same early tuple',
             'bound': '53/(k-1)+24/k', 'theorem': 'HelperJointGame.early_c1_wrong_claim_bound',
             'status': 'previous proved compact ideal field-game bound reused; source coupling pending',
             'overlap': 'contains four relation repairs once; not additive with previous image/row/near bounds'},
            {'class': 'same region, bound claims correct but checked witness not returned',
             'bound': None, 'status': 'early semantic/copy constraint enforcement, real decoder and complete payment/context/transition endpoint remain'},
            {'class': 'earlyC1=some; supported final distance>15334; specified extraction fails',
             'bound': None, 'status': 'new support bridge is conditional geometry, not a probability bound'},
            {'class': 'earlyC1=none; specified extraction fails',
             'bound': None, 'status': 'semantic16 recoverability must remain distinct from complete26 tuple absence'},
            {'class': 'private coefficient decoder failure given earlyC1=some and its precise ideal access/law prerequisites',
             'bound': 'previous conditional134.453-bit theorem, not recomposed here',
             'status': 'authenticated opening/replay access and concrete decoder refinement missing'},
        ],
        'partition_status': 'precedence/obligation map, not a completed source/extractor probability partition',
        'global_accepted_extraction_bound': None,
        'remaining_global_allowance': None,
        'body_bytes': body,
        'new_proof_body_values': 0,
        'new_verifier_operations': 0,
        'production_or_verifier_changes': False,
        'new_prover_SBF_or_complete_transaction_CU_measurement': False,
        'full_view_ZK': 'open',
        'resource_bounded_Fiat_Shamir': 'open; no grinding credit',
    }


if __name__ == '__main__':
    out = result()
    if sys.argv[1:] == ['--check-recorded']:
        assert json.loads((evidence.ROOT / 'recovery-interfaces-evidence.json').read_text()) == out
        print('Recovery/interface current-source evidence, exact controls and axioms match.')
    else:
        assert not sys.argv[1:]
        print(json.dumps(out, indent=2))
