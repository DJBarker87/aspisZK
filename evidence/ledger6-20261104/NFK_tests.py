#!/usr/bin/env python3
"""Mutations of the actual merged occurrence certificates and audit receipts."""
import copy
import unittest
from unittest.mock import patch
import NFK_validate as v

class Mutations(unittest.TestCase):
 @classmethod
 def setUpClass(cls):
  raw=(v.E/'NFK_LEDGER.json.xz').read_bytes()
  import lzma
  decoded=lzma.decompress(raw)
  v.require(v.sha(decoded)==(v.E/'NFK_LEDGER.json.sha256').read_text().strip(),'test ledger transport')
  import json
  cls.ledger=json.loads(decoded)
  cls.base=v.Corpus().obj('evidence/ledger5-20261104/NEZ_LEDGER.json')
  v.BASE_CREDITS=cls.base['NEZ_credits']
  cls.rows={r['row']:r for r in cls.ledger['rows']}
  cls.certs=cls.ledger['NFK_certificates']
  cls.target=next(r for r in cls.ledger['rows'] if r['composed_status']=='CLOSED' and r['row'] in cls.certs and r['row'] not in v.NEV_ROWS)

 def admitted(self,row=None,cert=None,audit=True):
  row=copy.deepcopy(row or self.target);rid=row['row']
  cert=self.certs[rid] if cert is None else cert
  out=v.admit(self.base,{rid:('mutation',row)},{rid:cert},{'mutation':[rid]},audit,'mutated audit receipt')
  return out,next(r for r in out['rows'] if r['row']==rid)

 def test_actual_nev_audit_admitted(self):
  self.assertTrue(self.ledger['NFK_nev_audit']['admitted'],self.ledger['NFK_nev_audit']['reason'])

 def test_real_certificate_admitted(self):
  self.assertEqual(self.admitted()[1]['composed_status'],'CLOSED')

 def test_missing_certificate_keeps_row_open(self):
  out,row=self.admitted(cert={})
  self.assertEqual(row['composed_status'],'OPEN')
  self.assertTrue(out['NFK_rejected_slice_closures'])

 def test_each_new_root_needs_certificate(self):
  functions={r['function'] for s in self.ledger['NFK_slices'].values() for r in s['roots']}
  roots=[r for r in self.ledger['rows'] if r['row'] in self.certs and r['function'] in functions]
  self.assertGreaterEqual(len(roots),5)
  for row in roots:
   with self.subTest(row=row['row']):self.assertEqual(self.admitted(row,cert={})[1]['composed_status'],'OPEN')

 def test_runtime_return_data_tag(self):
  cert={'selected':self.certs[self.target['row']],'runtime_assumption':'RuntimeReturnData'}
  self.assertIn('RuntimeReturnData',self.admitted(cert=cert)[1]['NFK_trust_rows'])

 def test_runtime_memcmp_tag(self):
  cert={'selected':self.certs[self.target['row']],'runtime_assumption':'RuntimeMemcmp'}
  self.assertIn('RuntimeMemcmp',self.admitted(cert=cert)[1]['NFK_trust_rows'])

 def test_both_added_trust_rows_tagged(self):
  cert={'selected':self.certs[self.target['row']],'assumptions':['RuntimeMemcmp','RuntimeReturnData']}
  self.assertEqual(self.admitted(cert=cert)[1]['NFK_trust_rows'],['RuntimeMemcmp','RuntimeReturnData'])

 def test_actual_runtime_consumers(self):
  emitter=next(r for r in self.ledger['rows'] if r['function'].endswith('::emit_result'))
  scanner=next(r for r in self.ledger['rows'] if r['function'].endswith('::scan_proof_buffer'))
  self.assertIn('RuntimeReturnData',emitter['NFK_trust_rows'])
  self.assertIn('RuntimeMemcmp',scanner['NFK_trust_rows'])
  self.assertNotIn('RuntimeReturnData',scanner['NFK_trust_rows'])
  for name in v.TRUST:self.assertIn('ADDED',v.TRUST[name]['classification'])

 def test_qualified_rows_never_headline_closed(self):
  for rid in v.QUALIFIED:
   out,row=self.admitted(self.rows[rid])
   self.assertEqual(row['composed_status'],'QUALIFIED')
   self.assertNotIn(rid,[r['row'] for r in out['rows'] if r['composed_status']=='CLOSED'])
  self.assertEqual(set(self.ledger['NFK_qualified_rows']),v.QUALIFIED)

 def test_missing_ax2_receipt_denies_all_four_nev_rows(self):
  c=v.Corpus();original=c.lane
  def damaged(prefix,name):
   if prefix=='NFC' and name=='NFC_L005/receipt.json':raise FileNotFoundError('deleted fixture replay')
   return original(prefix,name)
  with patch.object(c,'lane',damaged):self.assertFalse(v.nev_audit(c)[0])
  candidates={rid:('NFC',self.rows[rid]) for rid in v.NEV_ROWS}
  out=v.admit(self.base,candidates,self.certs,{'NFC':sorted(v.NEV_ROWS)},False,'missing NFC_L005')
  self.assertTrue(all(r['composed_status']=='OPEN' for r in out['rows'] if r['row'] in v.NEV_ROWS))

 def test_nonstandard_nev_audit_denied(self):
  c=v.Corpus();original=c.lane
  def damaged(prefix,name):
   data=copy.deepcopy(original(prefix,name))
   if name=='NFA_AUDIT.json':data['attempts'][0]['print_axioms']=["'root' depends on axioms: [sorryAx]"]
   return data
  with patch.object(c,'lane',damaged):self.assertFalse(v.nev_audit(c)[0])

 def test_wrong_frozen_body_denied(self):
  row=copy.deepcopy(self.target);row['frozen_body_sha256']='0'*64
  self.assertEqual(self.admitted(row)[1]['composed_status'],'OPEN')

 def test_undischarged_caller_denied(self):
  row=copy.deepcopy(self.target);self.assertTrue(row['caller_domain_obligations'])
  row['caller_domain_obligations'][0]['discharged_by']=None
  self.assertEqual(self.admitted(row)[1]['composed_status'],'OPEN')

 def test_undischarged_hypothesis_denied(self):
  row=copy.deepcopy(self.target);row['named_hypotheses'][0]['discharged_by']=None
  self.assertEqual(self.admitted(row)[1]['composed_status'],'OPEN')

 def test_exact_rejection_reconciliation(self):
  reported={rid for ids in self.ledger['NFK_slice_validator_results'].values() for rid in ids}
  accepted={r['row'] for r in self.ledger['rows'] if r['composed_status']=='CLOSED'}
  self.assertEqual(reported-accepted,{r['row'] for r in self.ledger['NFK_rejected_slice_closures']})

 def test_inherited_trust_contracts_preserved(self):
  by={t['id']:t for t in self.ledger['trust_rows']}
  for original in self.base['trust_rows']:
   self.assertTrue(all(by[original['id']].get(k)==val for k,val in original.items()))

 def test_occurrence_inventory_preserved(self):
  identity=lambda d:[(r['row'],r['function'],r['frozen_body_sha256']) for r in d['rows']]
  self.assertEqual(identity(self.base),identity(self.ledger))
  self.assertEqual(self.base['quarantine'],self.ledger['quarantine'])
  self.assertEqual(self.base['NEZ_credits'],self.ledger['NEZ_credits'])

if __name__=='__main__':unittest.main(verbosity=2)
