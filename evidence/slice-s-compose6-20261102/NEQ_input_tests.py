from pathlib import Path
import tempfile,unittest,json,lzma,hashlib
from NEQ_inputs import read,write_delta
class Inputs(unittest.TestCase):
 def test_roundtrip(self):
  with tempfile.TemporaryDirectory(prefix='NEQ_') as d:
   p=Path(d)/'NEQ_LEDGER_DELTA.json';data={'certificate':'exact input','nested':[1,2]};write_delta(p,data);self.assertFalse(p.exists());self.assertEqual(read(p),data)
 def test_wrong_uncompressed_hash_rejected(self):
  with tempfile.TemporaryDirectory(prefix='NEQ_') as d:
   p=Path(d)/'NEQ_LEDGER_DELTA.json';write_delta(p,{'certificate':1});Path(str(p)+'.sha256').write_text('0'*64)
   with self.assertRaises(AssertionError):read(p)
 def test_wrong_payload_with_retained_hash_rejected(self):
  with tempfile.TemporaryDirectory(prefix='NEQ_') as d:
   p=Path(d)/'NEQ_LEDGER_DELTA.json';write_delta(p,{'certificate':1});Path(str(p)+'.xz').write_bytes(lzma.compress(b'{"certificate":2}\n'))
   with self.assertRaises(AssertionError):read(p)
 def test_missing_hash_rejected(self):
  with tempfile.TemporaryDirectory(prefix='NEQ_') as d:
   p=Path(d)/'NEQ_LEDGER_DELTA.json';write_delta(p,{'certificate':1});Path(str(p)+'.sha256').unlink()
   with self.assertRaises(FileNotFoundError):read(p)
 def test_no_unrelated_fallback(self):
  with tempfile.TemporaryDirectory(prefix='NEQ_') as d:
   p=Path(d)/'missing.json'
   with self.assertRaises(AssertionError):read(p)
if __name__=='__main__':unittest.main(verbosity=2)
