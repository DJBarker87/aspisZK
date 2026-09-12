import sys,unittest
from pathlib import Path
sys.path.insert(0,str(Path(__file__).resolve().parents[1]/'tools'))
from toolchain_policy import parse_version,validation_permitted
class ToolchainTests(unittest.TestCase):
    def test_old_pin_is_reproduction_only(self):
        self.assertFalse(validation_permitted('Lean (version 4.32.0, x86_64, Release)'))
        self.assertFalse(validation_permitted('Lean (version 4.32.1, x86_64, Release)'))
    def test_patched_minimum(self):
        self.assertTrue(validation_permitted('Lean (version 4.32.2, x86_64, Release)'))
    def test_unrecognised_fails(self):
        with self.assertRaises(ValueError):parse_version('unknown compiler')
