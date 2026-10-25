"""Tiny real Acquisition/Reader API fixtures; only OS calls are mocked."""
import importlib.util
from pathlib import Path
import time
import unittest
from unittest.mock import patch
import FinalNativeGate_candidate as c
import FinalNativeGate_bounded as b
spec=importlib.util.spec_from_file_location('tree028',Path(__file__).with_name('FinalNativeGate-v4-tests.py'))
f=importlib.util.module_from_spec(spec);spec.loader.exec_module(f)

class DataTraversal(unittest.TestCase):
    def acquire(self,mode=0o40775,uid=1000,gid=1000,data_only=True):
        root='/home/dombarker/.cargo';path=root+'/registry/src/file'
        t=f.Tree({'STAGE':path})
        t.nodes[root]=dict(mode=mode,raw=bytearray(),uid=uid)
        t.nodes[path]=dict(mode=0o100644,raw=bytearray(b'actual fixture'),uid=1000)
        original=t.stat
        def stat(name,dir_fd=None,follow_symlinks=False):
            s=original(name,dir_fd,follow_symlinks);s.st_gid=gid if t.path(name,dir_fd)==root else 1000;return s
        t.stat=stat
        self.enterContext(patch.object(c,'os',t.api));self.enterContext(patch.object(b,'os',t.api))
        # Tree's bound stat in api must use the modified exact gid fixture too.
        t.api.stat=stat
        a=c.Acquisition(time.monotonic()+10,data_only=data_only);a.add(path)
        return a,t,root,path
    def test_data_775_hash_and_record_and_strict_default(self):
        a,t,root,path=self.acquire();s=a.snapshot()
        self.assertIn(path,s['pins']);row=s['trusted_group_directories'][0]
        self.assertEqual((row['path'],row['mode'],row['uid'],row['gid']),(root,0o40775,1000,1000))
        self.assertIn('no-concurrent-untrusted-writer',row['operational_trust'])
        with self.assertRaisesRegex(b.CatalogError,'writable'):
            b.Reader(a.catalog()).pin(path)
        self.assertFalse(t.fds)
        with self.assertRaisesRegex(b.CatalogError,'fixed source hash drift'):
            c.verify_expected(s,{path:'0'*64})
    def test_strict_acquisition_rejects_775(self):
        a,t,root,path=self.acquire(data_only=False)
        self.assertNotIn(path,a.snapshot()['pins']);self.assertEqual(a.unresolved[-1]['outcome'],'rejected')
    def test_other_permissions_and_owners_rejected(self):
        for mode,uid,gid in [(0o40777,1000,1000),(0o40775,999,1000),(0o40775,1000,999),(0o100664,1000,1000)]:
            with self.subTest(mode=mode,uid=uid,gid=gid):
                a,t,root,path=self.acquire(mode,uid,gid)
                self.assertNotIn(path,a.snapshot()['pins']);self.assertEqual(a.unresolved[-1]['outcome'],'rejected')
    def test_all_ancestors_and_unknown_are_rechecked(self):
        a,t,root,path=self.acquire();a.snapshot();t.nodes[root]['mode']=0o40755
        with self.assertRaisesRegex(b.CatalogError,'drift|changed'):a.snapshot()
    def test_writable_regular_leaf_and_unknown_metadata(self):
        a,t,root,path=self.acquire()
        t.nodes[path]['mode']=0o100664
        with self.assertRaisesRegex(b.CatalogError,'drift'):a.snapshot()
        other=root+'/registry/src/socket'
        t.nodes[other]=dict(mode=0o140600,raw=bytearray(),uid=1000)
        a.add(other)
        self.assertEqual(a.rows[other]['kind'],'unknown')
        self.assertNotIn(other,a.files)
        with self.assertRaisesRegex(b.CatalogError,'unknown entry'):
            b.Reader(a.catalog(),data_only=True).pin(other)
    def test_default_acquisition_and_all_actual_obstructions(self):
        for root in ('/home/dombarker/.kani','/home/dombarker/project-offloads/codex-cx-prover-rw-20261023'):
            a,t,_,_=self.acquire();path=root+'/file'
            parts=path.split('/')[1:-1];current=''
            for part in parts:
                current+='/'+part
                t.nodes.setdefault(current,dict(mode=0o40755,raw=bytearray(),uid=1000))
            t.nodes[root]=dict(mode=0o40775,raw=bytearray(),uid=1000)
            t.nodes[path]=dict(mode=0o100644,raw=bytearray(b'x'),uid=1000)
            strict=c.Acquisition(time.monotonic()+10);strict.add(path)
            self.assertNotIn(path,strict.snapshot()['pins'])
            a.add(path);self.assertIn(path,a.snapshot()['pins'])
    def test_json_cannot_enable_reader_mode(self):
        a,t,root,path=self.acquire();catalog=a.catalog();catalog['data_only']=True
        with self.assertRaisesRegex(b.CatalogError,'writable'):b.Reader(catalog).pin(path)

if __name__=='__main__':unittest.main()
