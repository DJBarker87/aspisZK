#!/usr/bin/env python3
"""Regression tests for authoritative exit vs live/unknown admission data."""
import errno, json, pathlib, tempfile, types, unittest
from unittest.mock import patch
import Port21PROJECTION_gate as gate
P=pathlib.Path
class GateTests(unittest.TestCase):
 def setUp(self):
  self.tmp=tempfile.TemporaryDirectory(); self.root=P(self.tmp.name); self.proc=self.root/'proc';self.proc.mkdir()
  self.rows=[dict(path='.',effective_cover=None,direct_ids=['123'])]
 def tearDown(self): self.tmp.cleanup()
 def path(self,*parts):
  s=str(P(*parts));return self.root/s.lstrip('/') if s.startswith('/proc') else P(*parts)
 def invoke(self,pin,poll):
  with patch.object(gate,'pathlib',types.SimpleNamespace(Path=self.path)), patch.object(gate.os,'pidfd_open',side_effect=pin,create=True), patch.object(gate.os,'close'),patch.object(gate.select,'poll',return_value=types.SimpleNamespace(register=lambda *a:None,poll=lambda _:poll)):
   return gate.processes(self.rows)
 def live(self):
  p=self.proc/'123';p.mkdir(); (p/'cgroup').write_text('0::/\n')
  fields=['S']+['0']*18+['456']+['0']*4
  (p/'stat').write_text('123 (test) '+' '.join(fields));(p/'status').write_text('VmRSS:\t12 kB\nVmSwap:\t0 kB\n')
  return p
 def test_confirmed_exit_after_pin(self):
  p=self.proc/'123';p.mkdir()
  rows,exits=self.invoke([77],[ (77,1) ]);self.assertFalse(rows);self.assertEqual(len(exits),1)
 def test_unreadable_live_denied(self):
  p=self.proc/'123';p.mkdir()
  with self.assertRaises(AssertionError): self.invoke([77],[])
 def test_kernel_esrch_revalidated_and_absent(self):
  rows,exits=self.invoke([ProcessLookupError(errno.ESRCH,'gone'),ProcessLookupError(errno.ESRCH,'gone')],[])
  self.assertFalse(rows);self.assertIn('two kernel',exits[0]['evidence'])
 def test_esrch_existing_proc_denied(self):
  (self.proc/'123').mkdir()
  with self.assertRaises(AssertionError):self.invoke([ProcessLookupError(errno.ESRCH,'gone'),ProcessLookupError(errno.ESRCH,'gone')],[])
 def test_replacement_identity_denied(self):
  with self.assertRaises(RuntimeError):self.invoke([ProcessLookupError(errno.ESRCH,'gone'),88],[])
 def test_live_metrics_recorded(self):
  self.live();rows,exits=self.invoke([77],[]);self.assertEqual(rows[0]['rss'],12288);self.assertFalse(exits)
 def test_missing_live_metric_denied(self):
  p=self.live();(p/'status').write_text('VmRSS:\t12 kB\n')
  with self.assertRaises(AssertionError):self.invoke([77],[])
if __name__=='__main__':
 suite=unittest.defaultTestLoader.loadTestsFromTestCase(GateTests)
 r=unittest.TextTestRunner(verbosity=2).run(suite)
 print(json.dumps(dict(schema='Port21PROJECTION-guard-tests-v1',tests=r.testsRun,failures=len(r.failures),errors=len(r.errors),print_axioms='N/A')))
 raise SystemExit(not r.wasSuccessful())
