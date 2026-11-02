"""Exact frozen projection, with fail-closed source mutation controls."""
from pathlib import Path
import subprocess,hashlib,json,unittest
E=Path(__file__).resolve().parent
PATH='crates/aspis-statement/src/pool_v1/pair_forest_terminal.rs'
REV='4bb3b3f51e16b4525f1d10336e2b0bcbbd775387'
EXPECTED='''pub fn common(&self) -> &PoolV1PairForestTerminalCommonV1 {
        match self {
            Self::PrivateTransfer { common, .. } | Self::Withdrawal { common, .. } => common,
        }
    }'''
def check(source):
 try:
  start=source.index('pub fn common(');end=source.index('\n    }',start)+6
  return source[start:end]==EXPECTED and source.count('pub fn common(')==1
 except ValueError:return False
class Mutations(unittest.TestCase):
 def test_original(self):self.assertTrue(check(EXPECTED))
 def test_different_place(self):self.assertFalse(check(EXPECTED.replace('=> common','=> other')))
 def test_changed_variant(self):self.assertFalse(check(EXPECTED.replace('Self::Withdrawal','Self::PrivateTransfer')))
 def test_duplicate(self):self.assertFalse(check(EXPECTED+EXPECTED))
 def test_missing(self):self.assertFalse(check(''))
if __name__=='__main__':
 r=unittest.TextTestRunner().run(unittest.defaultTestLoader.loadTestsFromTestCase(Mutations));assert r.wasSuccessful()
 source=subprocess.check_output(['git','show',REV+':'+PATH],text=True);assert check(source)
 (E/'NEL_GETTER_IDENTITY.json').write_text(json.dumps(dict(frozen_revision=REV,source=PATH,source_sha256=hashlib.sha256(source.encode()).hexdigest(),exact_projection=EXPECTED,accepted=True,mutation_tests=r.testsRun,extracted_identity='NED_ReconstructCarriers.common_argument',axioms_receipt='NEL_L001/receipt.json',classification='ruling y-prime pure borrowed field getter; P6/D188 option A reclassification'),indent=1)+'\n')
