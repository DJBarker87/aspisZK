"""Read-only diagnostic tests on fresh private fixtures; zero SSH calls."""
import ast, hashlib, importlib.util, json, os, stat, tempfile, unittest
from pathlib import Path
from types import SimpleNamespace
from unittest.mock import patch
D=Path(__file__).resolve().parent
spec=importlib.util.spec_from_file_location('diagnostic',D/'FinalNativeGate-receipt-diagnostic.py')
diag=importlib.util.module_from_spec(spec);spec.loader.exec_module(diag)
spec=importlib.util.spec_from_file_location('transport',D/'FinalNativeGate-receipt-transport.py')
transport=importlib.util.module_from_spec(spec);spec.loader.exec_module(transport)
class Diagnostic(unittest.TestCase):
    def setUp(self):
        self.root=Path(tempfile.mkdtemp(prefix='FinalNativeGate-receipt-diag-test-',dir='/private/tmp'))
        self.parts=('home','user','stage','packet');p=self.root
        for part in self.parts:p=p/part;p.mkdir(mode=0o700)
        self.packet=p
        for name in diag.NAMES:
            fd=os.open(p/name,os.O_WRONLY|os.O_CREAT|os.O_EXCL,0o600)
            with os.fdopen(fd,'wb') as f:f.write(b'{"error":"synthetic setup error"}')
        self.real_open=os.open;self.real_stat=os.stat
    def run_diag(self,groupwrite=False,drift=False,wrongowner=False):
        opened=[];closed=[];real_close=os.close;real_fstat=os.fstat
        def op(path,flags,*args,**kwargs):
            # Literal-root substitution exists ONLY in this test boundary. The
            # sealed remote script has no path argument or environment override.
            self.assertFalse(flags&(os.O_WRONLY|os.O_RDWR|os.O_CREAT))
            if path=='/':path=self.root
            fd=self.real_open(path,flags,*args,**kwargs);opened.append(fd);return fd
        def close(fd):closed.append(fd);return real_close(fd)
        calls={}
        def fstat(fd):
            s=real_fstat(fd);calls[fd]=calls.get(fd,0)+1
            if stat.S_ISREG(s.st_mode) and (wrongowner or (drift and calls[fd]>=2)):
                row={k:getattr(s,k) for k in dir(s) if k.startswith('st_')}
                row['st_uid' if wrongowner else 'st_ctime_ns']+=1
                return SimpleNamespace(**row)
            return s
        with patch.object(diag,'CHAIN',self.parts),patch.object(diag.os,'open',op),patch.object(diag.os,'close',close),patch.object(diag.os,'fstat',fstat):
            result=diag.collect()
        self.assertEqual(sorted(opened),sorted(closed));self.assertEqual(len(opened),len(set(opened)))
        return result
    def test_exact_three_success_only_terminal_json(self):
        result=self.run_diag();self.assertTrue(result['interval_stable']);self.assertFalse(result['trusted'])
        self.assertEqual(set(result['files']),set(diag.NAMES))
        for name,row in result['files'].items():
            self.assertTrue(row['original_receiver_predicate']);self.assertFalse(row['trusted'])
            self.assertEqual(row['sha256'],hashlib.sha256((self.packet/name).read_bytes()).hexdigest())
            self.assertEqual('untrusted_parsed_json' in row,name==diag.NAMES[0])
    def test_actual_groupwrite_data_exception_original_failure(self):
        # Change only newly allocated own fixtures; no external permissions.
        p=self.packet/diag.NAMES[0]
        os.chmod(p,0o660)
        r=self.run_diag()['files'][diag.NAMES[0]]
        self.assertFalse(r['original_receiver_predicate']);self.assertTrue(r['group_write_exception'])
        self.assertFalse(r['trusted']);self.assertIn('untrusted_parsed_json',r)
    def test_hardlink_symlink_worldwrite_and_oversize_denied(self):
        # Fresh root per subcase; retained fixtures never cleaned up/adopted.
        name=diag.NAMES[0];p=self.packet/name
        os.link(p,self.packet/'alias')
        r=self.run_diag();self.assertIn('error',r['files'][name]);self.assertNotIn('sha256',r['files'][name])
        p=self.packet/diag.NAMES[1];os.chmod(p,0o602)
        self.assertIn('error',self.run_diag()['files'][p.name])
        p=self.packet/diag.NAMES[2]
        with p.open('wb') as f:f.truncate(diag.FILE_LIMIT+1)
        self.assertIn('error',self.run_diag()['files'][p.name])
    def test_missing_and_symlink_metadata_without_follow(self):
        # No removal: use a separate fresh chain whose terminal never existed.
        p=self.packet/'other';p.mkdir(mode=0o700)
        os.symlink('../'+diag.NAMES[0],p/diag.NAMES[1])
        self.parts=(*self.parts,'other')
        r=self.run_diag();self.assertTrue(all('error' in x for x in r['files'].values()))
    def test_race_denied_all_data_removed_and_fds_closed(self):
        r=self.run_diag(drift=True);self.assertFalse(r['interval_stable'])
        self.assertTrue(r['errors']);self.assertTrue(all('sha256' not in x and 'untrusted_parsed_json' not in x for x in r['files'].values()))
    def test_open_owner_race_denied(self):
        r=self.run_diag(wrongowner=True)
        self.assertFalse(r['interval_stable'])
        self.assertTrue(all('error' in x for x in r['files'].values()))
    def test_duplicate_nonfinite_and_large_terminal_not_authority(self):
        p=self.packet/diag.NAMES[0]
        for raw in (b'{"x":1,"x":2}',b'{"x":NaN}',b'{"x":1e999}'):
            with p.open('wb') as f:f.write(raw)
            row=self.run_diag()['files'][p.name]
            self.assertIn('parse_error',row);self.assertIn('sha256',row);self.assertNotIn('untrusted_parsed_json',row)
        with p.open('wb') as f:f.write(b' '*65537)
        row=self.run_diag()['files'][p.name];self.assertIn('parse_error',row);self.assertNotIn('untrusted_parsed_json',row)
    def test_read_error_closes_every_fd(self):
        with patch.object(diag.os,'read',side_effect=OSError('synthetic read failure')):
            r=self.run_diag()
        self.assertTrue(all('error' in x for x in r['files'].values()))
    def test_fixed_payload_pin_and_disabled_mains(self):
        source=(D/'FinalNativeGate-receipt-diagnostic.py').read_bytes()
        active=source.replace(b"if __name__=='__main__':raise SystemExit(main())",b"if __name__=='__main__':raise SystemExit(diagnostic_entry())")
        self.assertEqual(active,transport.PAYLOAD.read_bytes())
        self.assertEqual(transport.PIN,dict(size=len(active),sha256=hashlib.sha256(active).hexdigest()))
        self.assertEqual(transport.ARGV,['/usr/bin/ssh','-T','-oBatchMode=yes','-oConnectTimeout=10','-oStrictHostKeyChecking=yes','-oClearAllForwardings=yes','-oForwardAgent=no','dombarker@100.108.41.90','/usr/bin/python3 -I -B -'])
        with patch.object(transport.subprocess,'Popen',side_effect=AssertionError('SSH forbidden')):
            self.assertEqual(transport.main(),78);self.assertEqual(diag.main(),78)
        ast.parse(active)
if __name__=='__main__':unittest.main(verbosity=2)
