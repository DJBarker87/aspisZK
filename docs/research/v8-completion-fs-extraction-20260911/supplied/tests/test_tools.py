import importlib.util,tempfile,unittest
from pathlib import Path
import sys
TOOLS=Path(__file__).resolve().parents[1]/'tools'
sys.path.insert(0,str(TOOLS))
from source_audit import strip_lean_comments,audit
from import_manifest import manifest

class ToolTests(unittest.TestCase):
    def test_nested_comment_lexer(self):
        text='/- outer /- sorry -/ axiom -/\ntheorem t : True := by trivial -- admit\n'
        out=strip_lean_comments(text)
        self.assertNotIn('sorry',out);self.assertNotIn('axiom',out);self.assertIn('theorem t',out)
    def test_unterminated(self):
        with self.assertRaises(ValueError):strip_lean_comments('/- x')
    def test_import_resolution_and_duplicates(self):
        with tempfile.TemporaryDirectory() as d:
            root=Path(d);a=root/'a';b=root/'b';a.mkdir();b.mkdir()
            (a/'One.lean').write_text('import Two\nimport Mathlib\n')
            (a/'Two.lean').write_text('theorem x : True := by trivial\n')
            good=manifest([a],['One'],['Mathlib'])
            self.assertEqual(good['status'],'RESOLVED_NOT_BUILT')
            self.assertEqual(good['topological_order'],['Two','One'])
            (b/'Two.lean').write_text('theorem x : True := by trivial\n')
            bad=manifest([a,b],['One'],['Mathlib'])
            self.assertEqual(bad['status'],'BLOCKED');self.assertTrue(bad['ambiguous'])
    def test_missing_import(self):
        with tempfile.TemporaryDirectory() as d:
            r=manifest([Path(d)],['Missing'],[])
            self.assertEqual(r['status'],'BLOCKED')
    def test_this_pack_has_no_lexical_admissions(self):
        result=audit(Path(__file__).resolve().parents[1])
        self.assertFalse(result['violations'])
