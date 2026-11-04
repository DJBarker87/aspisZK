"""Own transport path equals the already-replayed overlay byte for byte."""
import unittest,lzma,hashlib,tempfile,json
from pathlib import Path
from NEU_inputs import read
E=Path(__file__).resolve().parent
class Transport(unittest.TestCase):
 def test_identical_inherited_inputs(self):
  for suffix in ['.xz','.sha256']:
   self.assertEqual((E/('NEU_LEDGER_DELTA.json'+suffix)).read_bytes(),(E.parent/'slice-s-compose6-20261102'/('NEQ_LEDGER_DELTA.json'+suffix)).read_bytes())
  self.assertEqual((E/'NEU_REVIEWED_CERTIFICATES.json').read_bytes(),(E.parent/'slice-s-compose6-20261102/NEQ_REVIEWED_CERTIFICATES.json').read_bytes())
 def test_compressed_hash_required(self):
  with tempfile.TemporaryDirectory() as d:
   p=Path(d)/'NEU_LEDGER_DELTA.json';Path(str(p)+'.xz').write_bytes(lzma.compress(b'{}'));Path(str(p)+'.sha256').write_text('0'*64)
   with self.assertRaises(AssertionError):read(p)
 def test_valid_hash_transport(self):
  with tempfile.TemporaryDirectory() as d:
   p=Path(d)/'NEU_LEDGER_DELTA.json';raw=b'{"proof":"transport"}';Path(str(p)+'.xz').write_bytes(lzma.compress(raw));Path(str(p)+'.sha256').write_text(hashlib.sha256(raw).hexdigest());self.assertEqual(read(p),json.loads(raw))
if __name__=='__main__':unittest.main()
