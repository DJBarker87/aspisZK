"""Offline Acquisition regression: only the filesystem API is synthetic."""
import importlib.util
from pathlib import Path
import time
import unittest
from unittest.mock import patch
import FinalNativeGate_candidate as c
import FinalNativeGate_bounded as b

spec=importlib.util.spec_from_file_location('fixture_tree',Path(__file__).with_name('FinalNativeGate-v4-tests.py'))
f=importlib.util.module_from_spec(spec);spec.loader.exec_module(f)

class AcquisitionTests(unittest.TestCase):
    def tree(self):return f.Tree({'STAGE':c.STAGE+'/file'})
    def add_node(self,t,path,mode):
        t.nodes[path]=dict(mode=mode,raw=bytearray(),uid=123)
    def acquire(self,t):
        self.enterContext(patch.object(c,'os',t.api))
        self.enterContext(patch.object(b,'os',t.api))
        return c.Acquisition(time.monotonic()+10)
    def test_exact_stage_admitted_and_root_snapshot(self):
        t=self.tree();self.add_node(t,c.STAGE+'/file',0o100600)
        a=self.acquire(t);a.add(c.STAGE+'/file')
        self.assertIn(c.STAGE+'/file',a.snapshot()['pins'])
        a.add(c.STAGE+'-other/file')
        self.assertEqual(a.unresolved[-1]['outcome'],'excluded')
        self.assertFalse(t.fds)
    def test_775_ancestor_is_rejected_not_observed_missing(self):
        t=self.tree();root='/home/dombarker/.cargo'
        self.add_node(t,root,0o40775)
        a=self.acquire(t);path=root+'/registry/src/not-observed'
        a.add(path)
        self.assertEqual(a.unresolved[-1]['outcome'],'rejected')
        self.assertFalse(any(r.get('outcome')=='observed_missing' for r in a.unresolved))
        self.assertEqual(a.snapshot()['catalog']['entries'][root]['mode'],0o40775)
        with self.assertRaisesRegex(b.CatalogError,'writable'):
            with b.Reader(a.catalog()).opened(root):pass
    def test_known_missing_and_socket_metadata(self):
        t=self.tree();a=self.acquire(t);a.add(c.STAGE+'/absent')
        self.assertEqual(a.unresolved[-1]['outcome'],'observed_missing')
        path=c.STAGE+'/socket';self.add_node(t,path,0o140600);a.add(path)
        snapshot=a.snapshot()
        self.assertEqual(snapshot['catalog']['entries'][path]['kind'],'unknown')
        self.assertNotIn(path,snapshot['pins'])
        with self.assertRaisesRegex(b.CatalogError,'unknown entry'):
            with b.Reader(a.catalog()).opened(path):pass

if __name__=='__main__':unittest.main()
