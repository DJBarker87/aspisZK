"""Small source-only regression checks; no Lean, compiler, or external service."""
import contextlib
import importlib.util
import io
from pathlib import Path
import tempfile
import unittest
from unittest import mock

SPEC = importlib.util.spec_from_file_location('ledger_check', Path(__file__).with_name('check.py'))
CHECK = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(CHECK)
ROOT = Path(__file__).resolve().parents[2]


class DeclarationTests(unittest.TestCase):
    def test_namespaces_sections_and_fields(self):
        source = '''noncomputable section
namespace A.B
structure Trust (x : Nat)
    : Prop where
  law : x = x
section inner
private theorem local_result : True := True.intro
end inner
end A.B
end
'''
        self.assertEqual(CHECK.declarations(source), {'A.B.Trust', 'A.B.Trust.law', 'A.B.local_result'})

    def test_comments_and_strings_do_not_declare(self):
        source = '''/- outer /- theorem fake : False -/ comment -/
-- theorem fake : False
namespace A
 def text := "theorem fake : False"
theorem real : True := True.intro
end A
'''
        self.assertEqual(CHECK.declarations(source), {'A.text', 'A.real'})

    def test_wrong_namespace_is_absent(self):
        names = CHECK.declarations('namespace Actual\ntheorem present : True := True.intro\nend Actual\n')
        self.assertNotIn('Wrong.present', names)
        self.assertNotIn('present', names)

    def test_record_value_is_not_record_field(self):
        names = CHECK.declarations('namespace A\nstructure T where\n  field : True\ndef value : T where\n  field := True.intro\nend A\n')
        self.assertEqual(names, {'A.T', 'A.T.field', 'A.value'})

    def test_unterminated_comment_fails(self):
        with self.assertRaises(ValueError):
            CHECK.declarations('/- theorem hidden : True')

    def test_no_citations_fails(self):
        with tempfile.TemporaryDirectory() as directory:
            ledger = Path(directory) / 'ledger.md'
            ledger.write_text('Nothing cited.\n')
            with contextlib.redirect_stderr(io.StringIO()):
                self.assertEqual(CHECK.check(ROOT, ledger), (0, 1))

    def test_current_repository_positive_and_negative(self):
        # Keep relative links at the real ledger location without writing there.
        real = ROOT / 'design/RELEASE-LEDGER-20261025.md'
        content = real.read_text()
        positive, errors = CHECK.check(ROOT, real)
        self.assertGreater(positive, 100)
        self.assertEqual(errors, 0)
        target = 'AspisR1.Port6AUTH_Headline.final_soundness'
        changed = content.replace(target, target + '_does_not_exist')
        with mock.patch.object(Path, 'read_text', autospec=True) as read:
            # Source reads use saved bytes; only the ledger citation is corrupted.
            def read_text(path, *args, **kwargs):
                if path == real:
                    return changed
                return path.read_bytes().decode('utf-8')
            read.side_effect = read_text
            with contextlib.redirect_stderr(io.StringIO()):
                _, failures = CHECK.check(ROOT, real)
        self.assertGreater(failures, 0)

    def test_modified_source_cannot_claim_head_revision(self):
        real = ROOT / 'design/RELEASE-LEDGER-20261025.md'
        source = ROOT / 'docs/research/100bit-spend-path-20261013/lean/Port6AUTH_Headline.lean'
        original_read = Path.read_bytes
        def changed(path):
            data = original_read(path)
            return data + b'\n-- uncommitted source change\n' if path == source else data
        with mock.patch.object(Path, 'read_bytes', autospec=True, side_effect=changed):
            with contextlib.redirect_stderr(io.StringIO()) as errors:
                _, failures = CHECK.check(ROOT, real)
        self.assertGreater(failures, 0)
        self.assertIn('differs from HEAD', errors.getvalue())

    def test_path_escape_fails(self):
        with tempfile.TemporaryDirectory() as directory:
            outside = Path(directory) / 'outside.lean'
            outside.write_text('theorem fake : True := True.intro')
            ledger = Path(directory) / 'ledger.md'
            ledger.write_text(f'[`fake`]({outside}#decl=fake)')
            with contextlib.redirect_stderr(io.StringIO()):
                self.assertEqual(CHECK.check(ROOT, ledger), (1, 1))


if __name__ == '__main__':
    unittest.main()
