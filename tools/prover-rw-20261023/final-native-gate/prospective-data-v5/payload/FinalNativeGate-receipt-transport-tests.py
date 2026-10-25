"""Explicit transport syscall mocks only. No actual SSH/new DATA allocation."""
import importlib.util, json, os, resource, stat, subprocess, sys, tempfile, unittest
from pathlib import Path
from types import SimpleNamespace
from unittest.mock import patch
D=Path(__file__).resolve().parent
spec=importlib.util.spec_from_file_location('receipt_transport',D/'FinalNativeGate-receipt-transport.py')
t=importlib.util.module_from_spec(spec);spec.loader.exec_module(t)
class Transport(unittest.TestCase):
    def setUp(self):
        self.root=Path(tempfile.mkdtemp(prefix='FinalNativeGate-receipt-transport-mock-',dir='/private/tmp'))
        self.capture=self.root/'mock-only-capture';self.calls=[]
    def run_future(self,output=b'{"kind":"DiagnosticBytes"}\n',rss=b'1000\n1000\n',exit_pending=False):
        streams=[];usage=resource.getrusage(resource.RUSAGE_SELF)
        def popen(argv,**kwargs):
            self.calls.append(argv)
            self.assertEqual(argv,t.ARGV)
            self.assertTrue((self.capture/'exclusive-future-charge.json').exists())
            self.assertEqual(json.loads((self.capture/'exclusive-future-charge.json').read_bytes())['SSH_charge'],1)
            self.assertEqual(os.read(kwargs['stdin'],t.LIMIT),t.PAYLOAD.read_bytes())
            for data in (output,b''):
                r,w=os.pipe();os.write(w,data);os.close(w);streams.append(os.fdopen(r,'rb'))
            return SimpleNamespace(pid=987654321,stdout=streams[0],stderr=streams[1],returncode=None,kill=lambda:None)
        def wait4(pid,flags):return (pid,0,usage)
        with patch.object(t,'CAPTURE',self.capture),patch.object(t.sys,'argv',['transport-source']),patch.object(t.subprocess,'Popen',popen),patch.object(t.subprocess,'run',return_value=subprocess.CompletedProcess([],0,rss,b'')),patch.object(t.os,'wait4',wait4):
            code=t._reviewed_future()
        for f in streams:self.assertTrue(f.closed)
        return code
    def test_one_fixed_mock_charge_capture_no_overwrite(self):
        self.assertEqual(self.run_future(),0);self.assertEqual(len(self.calls),1)
        before={p.name:p.read_bytes() for p in self.capture.iterdir()}
        self.assertEqual(self.run_future(),78);self.assertEqual(len(self.calls),1)
        self.assertEqual(before,{p.name:p.read_bytes() for p in self.capture.iterdir()})
        for p in self.capture.iterdir():self.assertEqual(stat.S_IMODE(p.stat().st_mode),0o600)
    def test_memory_bound_kills_mock_and_retains_failure(self):
        self.assertEqual(self.run_future(rss=b'600000\n'),78)
        receipt=json.loads((self.capture/'receipt.json').read_bytes())
        self.assertIn('512MiB',receipt['errors'][0]);self.assertFalse(receipt['trusted'])
    def test_payload_pin_failure_has_no_launch(self):
        with patch.object(t,'PIN',dict(size=1,sha256='0'*64)):
            self.assertEqual(self.run_future(),78)
        self.assertEqual(self.calls,[])
        self.assertFalse((self.capture/'exclusive-future-charge.json').exists())
    def test_source_has_deadline_output_and_no_rlimit(self):
        source=(D/'FinalNativeGate-receipt-transport.py').read_text()
        self.assertIn('total>LIMIT',source);self.assertIn('time.monotonic()-start>=20',source)
        self.assertIn('os.WNOHANG',source);self.assertNotIn('setrlimit',source)
if __name__=='__main__':unittest.main(verbosity=2)
