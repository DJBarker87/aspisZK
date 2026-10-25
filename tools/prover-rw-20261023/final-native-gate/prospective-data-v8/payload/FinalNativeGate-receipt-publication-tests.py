"""Actual private filesystem fixtures plus explicit syscall/terminal mocks."""
import hashlib, importlib.util, json, os, runpy, stat, tempfile, unittest
from pathlib import Path
from types import SimpleNamespace
from unittest.mock import patch
import FinalNativeGate_setup as setup
D=Path(__file__).resolve().parent

def root():
    p=Path(tempfile.mkdtemp(prefix='FinalNativeGate-receipt-test-',dir='/private/tmp'))
    assert stat.S_IMODE(p.stat().st_mode)==0o700
    return p

def original(s):return stat.S_ISREG(s.st_mode) and s.st_nlink==1 and s.st_uid==os.getuid() and not s.st_mode&0o022

class Publication(unittest.TestCase):
    def setUp(self):
        self.packet=root();self.old_packet=setup.PACKET;setup.PACKET=self.packet
    def tearDown(self):setup.PACKET=self.old_packet
    def test_umask002_success_exact600_original_predicate(self):
        old=os.umask(0o002)
        try:r=setup._publish('terminal.json',{'bounded':'fixture','n':42})
        finally:os.umask(old)
        p=self.packet/r['name'];raw=p.read_bytes();s=p.stat()
        self.assertEqual(stat.S_IMODE(s.st_mode),0o600);self.assertTrue(original(s))
        self.assertEqual(r,dict(name=p.name,size=len(raw),sha256=hashlib.sha256(raw).hexdigest()))
        self.assertEqual(json.loads(raw),{'bounded':'fixture','n':42})
        print('retained actual post-repair fixture',self.packet)
    def test_restrictive_umask_fails_without_relaxation_retains_partial(self):
        old=os.umask(0o777)
        try:
            with self.assertRaises(ValueError):setup._publish('private.json',{})
        finally:os.umask(old)
        self.assertEqual(stat.S_IMODE((self.packet/'private.json').stat().st_mode),0)
    def test_existing_regular_symlink_hardlink_no_adoption(self):
        target=self.packet/'target'
        with target.open('xb') as f:f.write(b'unchanged')
        os.symlink('target',self.packet/'symlink');os.link(target,self.packet/'hardlink')
        for name in ('target','symlink','hardlink'):
            with self.assertRaises(FileExistsError):setup._publish(name,{})
        self.assertEqual(target.read_bytes(),b'unchanged');self.assertEqual(target.stat().st_nlink,2)
    def test_name_and_packet_denials(self):
        for name in ('../escape','a/b','','.','..','bad\0name'):
            with self.assertRaises(ValueError):setup._publish(name,{})
        alias=self.packet/'packet-alias';os.symlink(self.packet,alias);setup.PACKET=alias
        with self.assertRaises(ValueError):setup._publish('x',{})
    def test_wrong_owner_nlink_mode_mock_retained_and_closed(self):
        real=setup.os.fstat;real_close=setup.os.close
        for attr,value in (('st_uid',os.getuid()+1),('st_nlink',2),('st_mode',stat.S_IFREG|0o660)):
            closed=[]
            def fstat(fd):
                s=real(fd)
                if stat.S_ISREG(s.st_mode):
                    row={k:getattr(s,k) for k in dir(s) if k.startswith('st_')};row[attr]=value
                    return SimpleNamespace(**row)
                return s
            def close(fd):closed.append(fd);return real_close(fd)
            with patch.object(setup.os,'fstat',fstat),patch.object(setup.os,'close',close):
                with self.assertRaises(ValueError):setup._publish(attr+'.json',{})
            self.assertEqual(len(closed),2);self.assertTrue((self.packet/(attr+'.json')).exists())
    def test_write_and_sync_errors_propagate_partial_retained(self):
        real_sync=setup.os.fsync
        for case in ('write','file-sync','dir-sync'):
            path=self.packet/(case+'.json')
            def sync(fd):
                isdir=stat.S_ISDIR(os.fstat(fd).st_mode)
                if isdir==(case=='dir-sync'):raise OSError('synthetic '+case)
                return real_sync(fd)
            if case=='write':ctx=patch.object(setup.os,'write',side_effect=OSError('synthetic write'))
            else:ctx=patch.object(setup.os,'fsync',sync)
            with ctx:
                with self.assertRaises(OSError):setup._publish(path.name,{'fixture':case})
            self.assertTrue(path.exists());self.assertEqual(stat.S_IMODE(path.stat().st_mode),0o600)
    def test_short_writes_handled_zero_write_denied(self):
        real=setup.os.write
        with patch.object(setup.os,'write',lambda fd,b:real(fd,b[:1])):
            setup._publish('short.json',{'x':42})
        self.assertEqual(json.loads((self.packet/'short.json').read_bytes()),{'x':42})
        with patch.object(setup.os,'write',return_value=0):
            with self.assertRaises(OSError):setup._publish('zero.json',{})
        self.assertTrue((self.packet/'zero.json').exists())
    def test_late_link_and_entry_alias_denied(self):
        real=setup.json.JSONEncoder.iterencode
        def encoder(obj,value):
            os.link(self.packet/'link.json',self.packet/'retained-alias')
            yield from real(obj,value)
        with patch.object(setup.json.JSONEncoder,'iterencode',encoder):
            with self.assertRaises(ValueError):setup._publish('link.json',{})
        self.assertEqual((self.packet/'link.json').stat().st_nlink,2)
    def test_nonfinite_serialization_failure_retains_partial(self):
        with self.assertRaises(ValueError):setup._publish('nonfinite.json',{'n':float('inf')})
        self.assertTrue((self.packet/'nonfinite.json').exists())

if __name__=='__main__':
    # Reuse only current concrete parent orchestration mock cases. No historical
    # source or old action log is opened; no actual process/scope launch.
    prior=runpy.run_path(str(D/'FinalNativeGate-v4-tests.py'),run_name='source_fixture')
    suite=unittest.defaultTestLoader.loadTestsFromTestCase(Publication)
    for name in ('test_prior_write_fault_persisted_terminal_is_failed','test_terminal_write_fault_nonzero_and_no_forged_terminal','test_success_nonzero_child_and_unresolved_retained'):
        suite.addTest(prior['ParentTerminal'](name))
    result=unittest.TextTestRunner(verbosity=2).run(suite)
    raise SystemExit(not result.wasSuccessful())
