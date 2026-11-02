#!/usr/bin/env python3
"""Mutate real certificates and support records; no fabricated passing proof."""
import copy
import json
import unittest
from unittest.mock import patch
import NEN_validate as v


class UnifiedMutations(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.base = v.read(v.R / 'evidence/native-ledger3-20261029/NDT_LEDGER.json')
        cls.q = v.read(v.q.E / 'NEB_EDGES.json')
        cls.s = v.read(v.s.E / 'NEL_LEDGER_DELTA.json')
        cls.oq, cls.os, cls.delta = v.slice_results(cls.base, cls.q, cls.s)
        v.SLICES = v.read(v.R / (v.ndt.DESIGN + 'VERTICAL-SLICES-20261029.json'))['slices']
        v.Q_FUNCTIONS = set(v.SLICES['Q']['functions'])
        v.Q_EDGES = {e['obligation_id']: e for e in cls.q['edges'] + cls.q['inventory_edges']}
        inputs = v.Inputs()
        try:
            cls.credits, cls.latest = v.k3_inventory(inputs, [cls.s])
        finally:
            inputs.close()
        cls.target = 'crates/aspis-core/src/field.rs::M31::reduce_u64'
        cls.edge = cls.target + ' -> crates/aspis-core/src/field.rs::reduce_u64'

    def unified(self, oq=None, os=None, credits=None, packet_s=None):
        return v.unify(self.base, self.oq if oq is None else oq, self.os if os is None else os,
                       self.s if packet_s is None else packet_s,
                       copy.deepcopy(self.credits if credits is None else credits), self.latest)

    def assert_open(self, out, function):
        rs = [r for r in out['rows'] if r['function'] == function]
        self.assertTrue(rs)
        self.assertTrue(all(r['composed_status'] == 'OPEN' for r in rs))

    def test_original_validators_and_unified_counts(self):
        out = self.unified()
        self.assertEqual(self.delta['closed_count'], 66)
        self.assertEqual(sum(r['composed_status'] == 'CLOSED' for r in self.os['rows']), 22)
        self.assertEqual(out['coverage']['all_rows']['composed_status']['CLOSED'], 88)
        self.assertEqual(out['NEN_rejected_slice_closures'], [])

    def mutate_q_edge(self, change):
        packet = copy.deepcopy(self.q)
        change(next(e for e in packet['edges'] if e['edge'] == self.edge))
        raw, _ = v.q.extend(self.base, packet)
        return self.unified(oq=raw)

    def test_missing_certificate_keeps_real_caller_open(self):
        self.assert_open(self.mutate_q_edge(lambda e: e.update(certificate=None)), self.target)

    def test_wrong_certificate_keeps_real_caller_open(self):
        self.assert_open(self.mutate_q_edge(lambda e: e['certificate'].update(edge='wrong')), self.target)

    def test_missing_state_effect_part_keeps_caller_open(self):
        self.assert_open(self.mutate_q_edge(lambda e: e['certificate']['parts'].pop('state_ordered_effects')), self.target)

    def test_suspended_credit_blocks_caller_and_transitive_users(self):
        credits = copy.deepcopy(self.credits)
        r = next(r for r in self.oq['rows'] if r['function'] == self.target)
        record = next(x for x in self.latest['rows'] if x['row'] == 'NEB:' + r['row'])
        support = record['support_receipts'][0]
        credits[support]['k3_status'] = 'SUSPENDED'
        out = self.unified(credits=credits)
        self.assert_open(out, self.target)
        impacted = [r for r in out['rows'] if r['slice_reported_closed'] and support in r['active_support_receipts']]
        self.assertTrue(impacted)
        self.assertTrue(all(r['composed_status'] == 'OPEN' for r in impacted))
        self.assertTrue(out['NEN_rejected_slice_closures'])

    def test_k2_quarantine_has_no_support_even_if_k3_restored(self):
        credits = copy.deepcopy(self.credits)
        r = next(r for r in self.oq['rows'] if r['function'] == self.target)
        record = next(x for x in self.latest['rows'] if x['row'] == 'NEB:' + r['row'])
        support = record['support_receipts'][0]
        credits[support].update(k3_status='RESTORED', k2_quarantined=True)
        out = self.unified(credits=credits)
        self.assert_open(out, self.target)
        self.assertTrue(any('K-2' in x for r in out['rows'] if r['function'] == self.target for x in r['NEN_rejections']))

    def test_unknown_credit_has_no_support(self):
        self.assertEqual(len(v.support_gate(['missing'], {})), 1)

    def test_open_credit_has_no_support(self):
        self.assertTrue(v.support_gate(['p'], {'p': {'k3_status': 'OPEN'}}))

    def test_s_missing_getter_certificate_keeps_row_open(self):
        packet = copy.deepcopy(self.s)
        packet['members'].pop(v.s.GETTER)
        raw = v.s.compose(self.base, packet, v.read(v.s.E / 'NEL_REVIEWED_CERTIFICATES.json'))
        self.assert_open(self.unified(os=raw, packet_s=packet), v.s.GETTER)

    def test_s_wrong_call_domain_keeps_row_open(self):
        packet = copy.deepcopy(self.s)
        packet['members'][v.s.GETTER]['call_domain_certificate']['subject'] = 'wrong'
        raw = v.s.compose(self.base, packet, v.read(v.s.E / 'NEL_REVIEWED_CERTIFICATES.json'))
        self.assert_open(self.unified(os=raw, packet_s=packet), v.s.GETTER)

    def test_ruling_y_prime_gate_remains_required_after_review(self):
        packet = copy.deepcopy(self.s)
        c = packet['members'][v.s.GETTER]
        c['borrowed_projection']['all_typed_inputs'] = False
        c.pop('semantic_review_sha256')
        digest = v.sha(json.dumps(c, sort_keys=True).encode())
        c['semantic_review_sha256'] = digest
        review = dict(v.read(v.s.E / 'NEL_REVIEWED_CERTIFICATES.json'), **{v.s.GETTER: digest})
        raw = v.s.compose(self.base, packet, review)
        self.assert_open(self.unified(os=raw, packet_s=packet), v.s.GETTER)

    def test_inherited_certificate_denial_is_not_bypassed(self):
        c = self.s['members'][v.s.GETTER]
        with patch.object(v.s.predecessor.predecessor, 'BASE_CERTIFICATE', return_value=False):
            self.assertFalse(v.s.certificate(c, v.s.GETTER, self.base, v.read(v.s.E / 'NEL_REVIEWED_CERTIFICATES.json')))

    def test_original_ndt_rejects_forged_baseline_closed(self):
        b = copy.deepcopy(self.base)
        b['rows'][0]['composed_status'] = 'CLOSED'
        with self.assertRaises((AssertionError, ValueError, KeyError)):
            v.ndt.validate_invariants(b)

    def test_coverage_counts_unique_functions_separately(self):
        out = self.unified()
        self.assertEqual(out['coverage']['TX1']['rows'], 345)
        self.assertEqual(out['coverage']['TX2']['rows'], 242)
        self.assertEqual(sum(out['coverage']['unique_functions']['composed_status'].values()), out['coverage']['unique_functions']['count'])

    def test_missing_materialized_input_fails(self):
        inputs = v.Inputs()
        path = 'evidence/slice-q-compose-20261029/NEB_EDGES.json'
        try:
            inputs.deleted.add(path)
            with self.assertRaisesRegex(ValueError, 'deleted input'):
                inputs.raw(path)
        finally:
            inputs.close()

    def test_wrong_input_hash_fails(self):
        inputs = v.Inputs()
        try:
            with self.assertRaisesRegex(ValueError, 'input hash'):
                inputs.raw('evidence/slice-q-compose-20261029/NEB_EDGES.json', '0' * 64)
        finally:
            inputs.close()

    def test_timeout_replacement_needs_accepted_formal_assembly(self):
        inputs = v.Inputs()
        original = inputs.obj
        def damaged(path):
            value = original(path)
            if path.endswith('NEK_L003/receipt.json'):
                value['exit_status'] = 1
            return value
        try:
            with patch.object(inputs, 'obj', damaged):
                with self.assertRaisesRegex(ValueError, 'missing formal assembly'):
                    v.k3_inventory(inputs, [self.s])
        finally:
            inputs.close()

    def test_timeout_replacement_needs_matched_nibble_control(self):
        inputs = v.Inputs()
        original = inputs.obj
        def damaged(path):
            value = original(path)
            if path.endswith('NEK_K236/receipt.json'):
                value['exit_status'] = 124
            return value
        try:
            with patch.object(inputs, 'obj', damaged):
                with self.assertRaisesRegex(ValueError, 'invalid restoration pair'):
                    v.k3_inventory(inputs, [self.s])
        finally:
            inputs.close()

    def test_local_packets_and_source_certificate_do_not_grant_composition(self):
        out = self.unified()
        inputs = v.Inputs()
        try:
            v.packet_audit(inputs, out, copy.deepcopy(self.credits))
        finally:
            inputs.close()
        self.assertEqual(out['coverage']['all_rows']['composed_status']['CLOSED'], 88)
        dispositions = out['NEN_packet_dispositions']
        self.assertEqual(len(dispositions), 7)
        self.assertTrue(all(not x['composed_rows'] for x in dispositions if 'NEC::' in x.get('claim', '')))
        self.assertTrue(all(c['admissible_local_credit'] == c['effective_local_credit'] for c in out['claims']))


if __name__ == '__main__':
    unittest.main(verbosity=2)
