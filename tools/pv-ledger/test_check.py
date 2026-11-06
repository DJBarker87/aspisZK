"""Checker controls using synthetic receipts, never evidence for a Lean theorem."""
import copy
import importlib.util
import json
from pathlib import Path
import unittest
from unittest.mock import patch

spec = importlib.util.spec_from_file_location('ledger_check', Path(__file__).with_name('check.py'))
check = importlib.util.module_from_spec(spec)
spec.loader.exec_module(check)

class ClosureControls(unittest.TestCase):
    def setUp(self):
        self.row = dict(id='thread:test',path='thread',kind='BODY',emitted_kind='Structured',
            status='CLOSED',callees=[],contract=dict(lean_pre='Test.Pre',lean_post='Test.Post',
            lean_contract='Test.Contract',lean_theorem='Test.contract'))
        self.source = 'namespace Test\ntheorem contract (s : Nat) (h : Test.Pre s) : Test.Post s\n'
        digest = check.sha(self.source.encode())
        self.row['closure'] = dict(theorem='Test.contract',branch='test',
            source=dict(path='test-source',revision='a'*40,sha256=digest),
            statement=dict(path='test-statement'),raw_audit=dict(path='test-audit'),
            raw_audit_source_sha256=digest,boundary='CALL_ENTRY_TO_RETURN',
            callee_instantiations=[],all_reply_branches=['returned','failure','divergence','pending'],frame_proved_by_shape=True)
        text = 'theorem Test.contract : ∀ (s : Nat) (h : Test.Pre s), Test.Post s'
        self.statement = dict(format='pv-ledger-printed-statement-v1',theorem='Test.contract',source_sha256=digest,
            printed_statement=text,printed_statement_sha256=check.sha(text.encode()),binders=[
                dict(verbatim='(s : Nat)',role='parameter',type_checked_non_proposition=True),
                dict(verbatim='(h : Test.Pre s)',role='hypothesis',category='Pre')])
        self.audit = dict(mode='raw_walk',source_revision='a'*40,complete=True,unresolved_constants=0,
            failures=[],standard_axioms_only=True,roots_requested=1,roots_completed=1,roots=[dict(
                root='Test.contract',source_sha256=digest,walked_axioms=['propext'],equal=True,standard_axioms_only=True)])

    def run_control(self):
        def read(ref):
            return {'test-source':self.source.encode(), 'test-statement':json.dumps(self.statement).encode(),
                    'test-audit':json.dumps(self.audit).encode()}[ref['path']]
        with patch.object(check,'read_ref',side_effect=read),patch.object(check,'git',return_value=b''):
            check.check_closed(self.row,{self.row['id']:self.row})

    def test_complete_synthetic_receipt(self): self.run_control()
    def test_missing_named_theorem(self):
        self.source='namespace Test\ndef other : Nat'
        with self.assertRaisesRegex(check.Invalid,'theorem absent'): self.run_control()
    def test_raw_audit_unresolved(self):
        self.audit['unresolved_constants']=1
        with self.assertRaisesRegex(check.Invalid,'incomplete raw audit'): self.run_control()
    def test_nonstandard_axiom(self):
        self.audit['roots'][0]['walked_axioms']=['sorryAx']
        with self.assertRaisesRegex(check.Invalid,'nonstandard'): self.run_control()
    def test_aggregate_pass_without_root(self):
        self.audit['roots']=[]
        with self.assertRaisesRegex(check.Invalid,'missing/duplicated'): self.run_control()
    def test_summary_audit_not_raw(self):
        self.audit['mode']='print_axioms'
        with self.assertRaisesRegex(check.Invalid,'not raw'): self.run_control()
    def test_audit_wrong_revision(self):
        self.audit['source_revision']='b'*40
        with self.assertRaisesRegex(check.Invalid,'revision differs'): self.run_control()
    def test_audit_wrong_source(self):
        self.audit['roots'][0]['source_sha256']='wrong'
        with self.assertRaisesRegex(check.Invalid,'root/source'): self.run_control()
    def test_unlisted_hypothesis(self):
        self.statement['binders'][1]['category']='receiver'
        with self.assertRaisesRegex(check.Invalid,'outside B-y'): self.run_control()
    def test_omitted_binder(self):
        self.statement['binders'].pop()
        with self.assertRaisesRegex(check.Invalid,'not exhaustive'): self.run_control()
    def test_bad_printed_hash(self):
        self.statement['printed_statement']+=' altered'
        with self.assertRaisesRegex(check.Invalid,'text hash'): self.run_control()
    def test_body_child_unclosed(self):
        child=copy.deepcopy(self.row); child['id']='thread:child'; child['status']='OPEN'
        self.row['callees']=[child['id']]
        self.row['closure']['callee_instantiations']=[dict(row=child['id'])]
        def read(ref):
            return {'test-source':self.source.encode(),'test-statement':json.dumps(self.statement).encode(),
                'test-audit':json.dumps(self.audit).encode()}[ref['path']]
        with patch.object(check,'read_ref',side_effect=read),patch.object(check,'git',return_value=b''):
            with self.assertRaisesRegex(check.Invalid,'not CLOSED'):
                check.check_closed(self.row,{self.row['id']:self.row,child['id']:child})
    def test_missing_frame(self):
        self.row['closure']['frame_proved_by_shape']=False
        with self.assertRaisesRegex(check.Invalid,'frame'): self.run_control()
    def test_pending_omitted(self):
        self.row['closure']['all_reply_branches'].pop()
        with self.assertRaisesRegex(check.Invalid,'branches incomplete'): self.run_control()
    def test_promote_real_partial_without_receipt(self):
        data=json.loads(check.DEFAULT.read_text())
        row=next(r for r in data['rows'] if r['status']=='PARTIAL')
        row['status']='CLOSED'
        self.assertTrue(any('no closure receipt' in e for e in check.validate(data)))
    def test_drop_real_row(self):
        data=json.loads(check.DEFAULT.read_text()); data['rows'].pop()
        self.assertTrue(any('enumeration rows' in e for e in check.validate(data)))
    def test_mutate_real_callee(self):
        data=json.loads(check.DEFAULT.read_text()); data['rows'][0]['callees']=[]
        self.assertTrue(any('enumeration drift' in e for e in check.validate(data)))

if __name__=='__main__': unittest.main()
