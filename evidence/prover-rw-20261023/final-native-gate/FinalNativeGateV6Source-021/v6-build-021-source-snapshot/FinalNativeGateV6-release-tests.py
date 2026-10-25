"""Exact v6 release gate; mock receiver filesystem and all runtime entries."""
import ast
import copy
import hashlib
import importlib.util
import json
from pathlib import Path
import stat
import sys
import tempfile
import unittest
E=Path(__file__).resolve().parent
D=E.parents[3]/'tools/prover-rw-20261023/final-native-gate'
R=D/'prospective-data-v6'
STAGE='/home/dombarker/final-native-gate-v6-20261025'

def module(name):
    spec=importlib.util.spec_from_file_location(name,D/(name+'.py'))
    m=importlib.util.module_from_spec(spec);spec.loader.exec_module(m);return m
old=module('FinalNativeGate-v4-tests');old.R=R

class V6(unittest.TestCase):
    def test_v6_literal_path_and_nonstage_identity(self):
        ns=old.receiver();self.assertEqual(ns['STAGE'],STAGE)
        p=json.loads(ns['decoded']()['FinalNativeGate-plan.json'])
        before=json.loads((E/'before-source020/FinalNativeGate-plan.json').read_bytes())
        a='/home/dombarker/final-native-gate-v5-20261025/'
        self.assertEqual({k:v for k,v in p['files'].items() if not k.startswith(STAGE+'/')},
                         {k:v for k,v in before['files'].items() if not k.startswith(a)})
        for key in before:
            if key not in ('files','job_source_sizes','job_revision','setup_catalog_roots'):self.assertEqual(p[key],before[key],key)
        self.assertEqual(sum(x is None for x in p.values()),7)
        self.assertEqual(set(p['setup_catalog_roots']),set(p['native_roots'])|set(p['files']))
        raw=(R/'FinalNativeGate-data-transfer.py').read_text()
        self.assertEqual(raw.count("'final-native-gate-v6-20261025'"),3)
        self.assertNotIn('final-native-gate-v5-20261025',raw.split('FILES=',1)[0])

    def test_new_leaf_mismatch_rejected_before_any_creation(self):
        ns=old.receiver();tree=old.Tree(ns);ns['os']=tree.api;before=copy.deepcopy(tree.nodes)
        ns['STAGE']='/home/dombarker/final-native-gate-v5-20261025'
        with self.assertRaisesRegex(ValueError,'leaf mismatch'):ns['install']()
        self.assertEqual(tree.nodes,before);self.assertFalse(tree.fds)

    def test_exact_current_uid_private_leaf_and_regular_files(self):
        ns=old.receiver();tree=old.Tree(ns);ns['os']=tree.api;ns['install']()
        self.assertEqual(tree.nodes[STAGE]['mode'],stat.S_IFDIR|0o700)
        self.assertEqual(tree.nodes[STAGE]['uid'],123)
        self.assertTrue(all(v['uid']==123 and v['mode']==stat.S_IFREG|0o600
                            for k,v in tree.nodes.items() if k.startswith(STAGE+'/')))

    def test_fresh_byte_identical_reproduction(self):
        builder=module('FinalNativeGate-data-release-build')
        tmp=Path(tempfile.mkdtemp(prefix='FinalNativeGateV6-reproduce-'))/'prospective-data-v6'
        builder.prepare(tmp)
        a={str(p.relative_to(R)):hashlib.sha256(p.read_bytes()).hexdigest() for p in R.rglob('*') if p.is_file()}
        b={str(p.relative_to(tmp)):hashlib.sha256(p.read_bytes()).hexdigest() for p in tmp.rglob('*') if p.is_file()}
        self.assertEqual(a,b)
        with (E/'reproduction.json').open('x') as f:
            json.dump(dict(byte_identical=True,files=len(a),sha256_by_relative_path=a,
                           reproduction_path=str(tmp),host_actions=0),f,sort_keys=True,indent=2)
            f.write('\n')

if __name__=='__main__':
    suite=unittest.TestSuite()
    for cls in (V6,old.Release):suite.addTests(unittest.defaultTestLoader.loadTestsFromTestCase(cls))
    for name in ('test_fresh_0775_ancestor_denied_and_secure_0750_accepted','test_preexisting_directory_regular_and_dangling_alias_denied','test_exact_coverage_and_manifest_tamper_denied'):
        suite.addTest(old.PathRepair(name))
    r=unittest.TextTestRunner(verbosity=2).run(suite);raise SystemExit(not r.wasSuccessful())
