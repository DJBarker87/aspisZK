"""Mutation tests of the strict overlay; synthetic records grant no proof credit."""
import copy, importlib.util, json, unittest
from unittest.mock import patch
from pathlib import Path
import NEE_validate as v
E=Path(__file__).resolve().parent
class OverlayControls(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.base=v.read(v.R/'evidence/native-ledger3-20261029/NDT_LEDGER.json')
        cls.packet=v.read(v.R/'evidence/slice-s-compose-20261029/NED_LEDGER_DELTA.json')
        cls.spec=v.read(v.R/'docs/research/100bit-spend-path-20261013/design/VERTICAL-SLICES-20261029.json')['slices']['S']
    def closed(self,p):
        return [r['row'] for r in v.compose(self.base,p,{})['rows'] if r['composed_status']=='CLOSED']
    def test_missing_certificates_leave_all_open(self):self.assertEqual(self.closed(self.packet),[])
    def test_wrong_edge_subject_leaves_all_open(self):
        p=copy.deepcopy(self.packet);edge=self.spec['internal_edges'][0]
        p['edges'][edge]={'kind':'call-domain','subject':edge+'wrong','frozen_revision':self.base['frozen_revision']}
        self.assertEqual(self.closed(p),[])
    def test_wrong_root_certificate_leaves_all_open(self):
        p=copy.deepcopy(self.packet);root=self.spec['roots'][1]
        p['roots'][root]={'kind':'root-composition','subject':root,'frozen_revision':self.base['frozen_revision'],'semantic_review_sha256':'0'*64}
        self.assertEqual(self.closed(p),[])
    def test_no_y_certificate_is_rejected(self):self.assertFalse(v.ruling_y({}))
    def test_model_only_is_rejected(self):self.assertFalse(v.certificate({'kind':'model-only'},'x',self.base,{}))
    def test_original_checker_is_necessary(self):
        with patch.object(v,'ruling_y',return_value=True):
            self.assertFalse(v.certificate({},'x',self.base,{}))
    def test_ruling_y_is_additional_not_replacement(self):
        with patch.object(v,'BASE_CERTIFICATE',return_value=True):
            self.assertFalse(v.certificate({'kind':'root-composition'},'x',self.base,{}))
    def test_baseline_drift_is_rejected(self):
        b=copy.deepcopy(self.base);b['rows'][0]['frozen_body_verified']=False
        with self.assertRaises(AssertionError):v.compose(b,self.packet,{})
    def test_base_hash_is_pinned(self):
        p=copy.deepcopy(self.packet);p['base_sha256']='0'*64
        with self.assertRaises(AssertionError):self.closed(p)
    def test_check_restored_after_exception(self):
        prior=v.inherited.certificate
        with self.assertRaises(KeyError):v.compose({},self.packet,{})
        self.assertIs(v.inherited.certificate,prior)

class RealCertificateMutations(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.base=v.read(v.R/'evidence/native-ledger3-20261029/NDT_LEDGER.json')
        cls.packet=v.read(E/'NEE_LEDGER_DELTA.json')
        cls.review=v.read(E/'NEE_REVIEWED_CERTIFICATES.json')
        cls.f=next(f for f in cls.packet['members'] if f.endswith('::transfer_common'))
    def rows(self,p,review=None):
        return [r['composed_status'] for r in v.compose(self.base,p,self.review if review is None else review)['rows'] if r['function']==self.f]
    def test_checked_leaf_closes(self):self.assertTrue(all(s=='CLOSED' for s in self.rows(self.packet)))
    def test_missing_leaf_certificate_keeps_row_open(self):
        p=copy.deepcopy(self.packet);p['members'].pop(self.f)
        self.assertTrue(all(s=='OPEN' for s in self.rows(p)))
    def test_suspended_static_module_keeps_m31_open(self):
        m=next(f for f in self.packet['members'] if f.endswith('::M31::to_le_bytes'))
        out=v.compose(self.base,self.packet,self.review)
        self.assertTrue(all(r['composed_status']=='OPEN' for r in out['rows'] if r['function']==m))
    def test_suspended_receipt_cannot_support_alternative_resolution(self):
        edge=next(e for e in self.packet['edges'] if 'M31::to_le_bytes ->' in e)
        self.assertFalse(v.certificate(self.packet['edges'][edge],edge,self.base,self.review))
    def test_missing_owned_shape_controls_keeps_row_open(self):
        with patch.object(v,'shape_admitted',return_value=False):
            self.assertTrue(all(s=='OPEN' for s in self.rows(self.packet)))
    def test_missing_frame_keeps_row_open(self):
        p=copy.deepcopy(self.packet);c=p['members'][self.f];c['direct_contract']['empty_modifies']=False
        self.assertTrue(all(s=='OPEN' for s in self.rows(p)))
    def test_wrong_theorem_even_if_resealed_keeps_row_open(self):
        p=copy.deepcopy(self.packet);review=copy.deepcopy(self.review);c=p['members'][self.f]
        c['direct_contract']['domain_and_model_theorems']=c['direct_contract']['domain_and_model_theorems'][1:]
        c.pop('semantic_review_sha256')
        c['semantic_review_sha256']=v.hashlib.sha256(json.dumps(c,sort_keys=True).encode()).hexdigest();review[self.f]=c['semantic_review_sha256']
        self.assertTrue(all(s=='OPEN' for s in self.rows(p,review)))
    def test_foreign_supplemental_edge_rejected(self):
        p=copy.deepcopy(self.packet);p['inventory_edges']['foreign -> foreign']={}
        with self.assertRaises(AssertionError):self.rows(p)

class ShapeAdmissionControls(unittest.TestCase):
    def test_complete_controls_admit_only_owned_supported_shapes(self):
        a=v.read(E/'NEE_SHAPE_ADMISSIONS.json')
        for shape in ['fixed4','common','tuple']:self.assertTrue(v.shape_admitted(shape,a[shape]))
        self.assertFalse(v.shape_admitted('borrowed',a['borrowed']))
    def test_missing_inverted_control_rejects_admission(self):
        a=copy.deepcopy(v.read(E/'NEE_SHAPE_ADMISSIONS.json')['fixed4'])
        del a['controls']['inverted']
        self.assertFalse(v.shape_admitted('fixed4',a))
    def test_codegen_failure_is_not_a_negative_control(self):
        a=copy.deepcopy(v.read(E/'NEE_SHAPE_ADMISSIONS.json')['fixed4'])
        a['controls']['unimplied']['stdout']={'path':str(E/'NEE_K039/stdout.log'),'sha256':v.hashlib.sha256((E/'NEE_K039/stdout.log').read_bytes()).hexdigest()}
        self.assertFalse(v.shape_admitted('fixed4',a))
    def test_wrong_carrier_rejects_admission(self):
        a=copy.deepcopy(v.read(E/'NEE_SHAPE_ADMISSIONS.json')['fixed4']);a['return_type']='[u8;8]'
        self.assertFalse(v.shape_admitted('fixed4',a))
    def test_boolean_alone_cannot_admit_new_shape(self):
        self.assertFalse(v.shape_admitted('fixed4',{'admitted':True}))

if __name__=='__main__':unittest.main()
