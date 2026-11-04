#!/usr/bin/env python3
"""Mutation checks over actual, fully checked NEZ row certificates."""
import copy
import unittest
from unittest.mock import patch
import NEZ_validate as v

class Mutations(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.ledger = v.read(v.E/'NEZ_LEDGER.json')
        cls.base = v.neo.baseline()
        cls.credits = {c['receipt']:c for c in cls.ledger['NEZ_credits']}
        cls.certs = cls.ledger['NEZ_certificates']
        cls.rows = {r['row']:r for r in cls.ledger['rows']}
        cls.target = next(r for r in cls.ledger['rows'] if r['composed_status']=='CLOSED' and r['row'] in cls.certs and r['active_support_receipts'])

    def unified(self,row=None,cert=None,credits=None):
        r=copy.deepcopy(row or self.target);rid=r['row']
        cert=copy.deepcopy(self.certs[rid] if cert is None else cert)
        return v.unify(self.base,{rid:('S',r)},{'mutation':[rid]},
                       {rid:cert},self.credits if credits is None else credits)

    def result_row(self,out,rid=None):
        return next(r for r in out['rows'] if r['row']==(rid or self.target['row']))

    def test_actual_certificate_accepted(self):
        self.assertEqual(self.result_row(self.unified())['composed_status'],'CLOSED')

    def test_missing_certificate_keeps_row_open(self):
        out=self.unified(cert={})
        self.assertEqual(self.result_row(out)['composed_status'],'OPEN')
        self.assertTrue(out['NEZ_rejected_slice_closures'])
        self.assertIn('Missing complete',out['NEZ_rejected_slice_closures'][0]['reasons'][0])

    def test_missing_root_certificate_keeps_each_closed_root_open(self):
        self.assertEqual(sum(root['status']=='CLOSED' for roots in self.ledger['NEZ_roots'].values() for root in roots),2)
        for roots in self.ledger['NEZ_roots'].values():
            for root in roots:
                if root['status']!='CLOSED':continue
                for rid in root['rows']:
                    out=self.unified(row=self.rows[rid],cert={})
                    self.assertEqual(self.result_row(out,rid)['composed_status'],'OPEN')

    def test_runtime_return_data_use_tagged(self):
        cert=copy.deepcopy(self.certs[self.target['row']])
        # A future otherwise valid certificate explicitly selecting this trust
        # must never acquire untagged composed credit.
        cert={'checked_certificate':cert,'runtime_assumption':'RuntimeReturnData'}
        out=self.unified(cert=cert)
        row=self.result_row(out)
        self.assertEqual(row['NEZ_trust_rows'],['RuntimeReturnData'])
        self.assertIn(row['row'],out['NEZ_ab_closed_native_rows'])
        self.assertTrue(any(t['id']=='RuntimeReturnData' and 'ADDED' in t['classification'] for t in out['trust_rows']))

    def test_model_theorem_reference_also_tags_trust(self):
        cert={'checked_certificate':self.certs[self.target['row']],
              'theorem':'NEX_EmitRuntime.result_state_effects'}
        self.assertEqual(self.result_row(self.unified(cert=cert))['NEZ_trust_rows'],['RuntimeReturnData'])

    def test_no_ab_closed_credit_in_real_checkpoint(self):
        self.assertEqual(self.ledger['NEZ_ab_uses']['closed_native_count'],0)
        self.assertEqual(self.ledger['NEZ_ab_uses']['closed_roots'],[])
        self.assertEqual(self.ledger['NEZ_ab_uses']['model_theorem_count'],5)

    def test_k3_suspension_denies_new_support(self):
        credits=copy.deepcopy(self.credits)
        path=self.target['active_support_receipts'][0]
        credits[path]['k3_status']='SUSPENDED'
        self.assertEqual(self.result_row(self.unified(credits=credits))['composed_status'],'OPEN')

    def test_k2_quarantine_not_lifted(self):
        credits=copy.deepcopy(self.credits)
        path=self.target['active_support_receipts'][0]
        credits[path].update(k3_status='RESTORED',k2_quarantined=True)
        self.assertEqual(self.result_row(self.unified(credits=credits))['composed_status'],'OPEN')

    def test_missing_hypothesis_denies(self):
        row=copy.deepcopy(self.target)
        self.assertTrue(row['named_hypotheses'])
        row['named_hypotheses'][0]['discharged_by']=None
        self.assertEqual(self.result_row(self.unified(row=row))['composed_status'],'OPEN')

    def test_missing_call_domain_denies(self):
        row=copy.deepcopy(next(r for r in self.ledger['rows'] if r['composed_status']=='CLOSED' and r['row'] in self.certs and r['caller_domain_obligations']))
        row['caller_domain_obligations'][0]['discharged_by']=None
        self.assertEqual(self.result_row(self.unified(row=row),row['row'])['composed_status'],'OPEN')

    def test_wrong_frozen_body_denies(self):
        row=copy.deepcopy(self.target);row['frozen_body_sha256']='0'*64
        with self.assertRaisesRegex(ValueError,'frozen identity'):self.unified(row=row)

    def test_unchanged_source_only_observer_stays_quarantined_historically(self):
        rows=[r for r in self.ledger['rows'] if 'NEO::deployed_mark_none' in r['selected_claims']]
        self.assertEqual(len(rows),2)
        self.assertTrue(all(r['composed_status']=='CLOSED' for r in rows))
        self.assertEqual(self.ledger['quarantine'],self.base['quarantine'])

    def test_original_trust_rows_preserved_addition_separate(self):
        self.assertEqual(self.ledger['trust_rows'][:-1],self.base['trust_rows'])
        self.assertEqual(self.ledger['trust_rows'][-1]['id'],'RuntimeReturnData')

    def test_inventories_and_occurrence_coverage_preserved(self):
        self.assertEqual([(r['row'],r['function'],r['frozen_body_sha256']) for r in self.ledger['rows']],
                         [(r['row'],r['function'],r['frozen_body_sha256']) for r in self.base['rows']])
        self.assertEqual(v.nen.coverage(self.ledger['rows']),self.ledger['coverage'])

    def test_newly_selected_open_inventory_entry_is_reviewed(self):
        path='evidence/slice-s-compose2-20261029/NEE_K052/receipt.json'
        old=next(c for c in self.base['NEN_credits'] if c['receipt']==path)
        self.assertEqual(old['k3_status'],'OPEN')
        new=v.new_credit(path,{path:old})
        self.assertEqual(new['k3_status'],'UNAFFECTED')
        self.assertEqual(new['NEZ_prior_review'],old)

    def test_source_review_cannot_restore_suspended_credit(self):
        path='evidence/slice-s-compose2-20261029/NEE_K052/receipt.json'
        denied=dict(receipt=path,k3_status='SUSPENDED',k2_quarantined=False)
        self.assertEqual(v.new_credit(path,{path:denied}),denied)

    def test_native_snapshot_hash_mutation_rejected(self):
        path='evidence/slice-q-compose3-20261102/NET_K039/receipt.json'
        original=v.read
        def damaged(p):
            d=original(p)
            if p==v.R/path:
                key=next(k for k in d['source_hashes'] if k.endswith('.rs'))
                d['source_hashes'][key]='0'*64
            return d
        with patch.object(v,'read',damaged):
            with self.assertRaisesRegex(ValueError,'native snapshot source hash'):
                v.new_credit(path,{})

    def test_d188_source_only_rows_have_no_native_credit(self):
        rows=[r for r in self.ledger['rows'] if r.get('NEZ_support_route','').startswith('D188_ACTUAL_BODY_')]
        self.assertEqual(len(rows),4)
        self.assertTrue(all(r['composed_status']=='CLOSED' and not r['active_support_receipts'] for r in rows))
        row=copy.deepcopy(rows[0]);row['frozen_body_sha256']='0'*64
        with self.assertRaisesRegex(ValueError,'D188 source route body'):
            v.source_routes({row['row']:('Q',row)},{row['row']:self.certs[row['row']]})

if __name__=='__main__':unittest.main(verbosity=2)
