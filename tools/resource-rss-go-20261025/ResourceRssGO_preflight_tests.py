"""Offline exact pre-staging bootstrap regression; no SSH or host retry."""
import ast
import builtins
import contextlib
import io
import json
from pathlib import Path
import tempfile
import unittest
from unittest.mock import patch
import ResourceRssGO_local as local
import ResourceRssGO_host as host

class ResourceRssGOPreflightTests(unittest.TestCase):
    def test_exact_unstaged_payload_imports_and_limit_capture(self):
        code=local.inspection_payload()
        tree=ast.parse(code)
        imports=[n.module for n in ast.walk(tree) if isinstance(n,ast.ImportFrom)]
        self.assertFalse(any((name or '').startswith('ResourceRssGO') for name in imports))
        original_import=builtins.__import__
        def isolated(name,*args,**kwargs):
            if name.startswith('ResourceRssGO'):raise AssertionError('unstaged module dependency')
            return original_import(name,*args,**kwargs)
        initial=host.inherited_limits()
        with tempfile.TemporaryDirectory() as tmp:
            stage=str(Path(tmp).resolve()/'not-created')
            code=code.replace(repr(local.REMOTE),repr(stage))
            tree=ast.parse(code)
            # Only runtime inventory is replaced: no Linux ELF/maps on Darwin.
            runtime=next(n for n in tree.body if isinstance(n,ast.FunctionDef) and n.name=='runtime_pins')
            runtime.body=[ast.Return(value=ast.Dict(keys=[],values=[]))]
            stream=io.StringIO()
            with patch.object(builtins,'__import__',isolated),contextlib.redirect_stdout(stream):
                exec(compile(ast.fix_missing_locations(tree),'ResourceRssGO-exact-preflight','exec'),{})
            observed=json.loads(stream.getvalue())
            self.assertEqual(observed['inherited_limits'],initial)
            self.assertFalse(observed['stage_exists'])
            self.assertFalse(Path(stage).exists())
        self.assertEqual(host.inherited_limits(),initial)

if __name__=='__main__':unittest.main(verbosity=2)
