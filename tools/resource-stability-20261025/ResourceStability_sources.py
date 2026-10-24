"""Immutable Git objects only. No filesystem scanner or live adapter is invoked."""
import ast
import hashlib
import subprocess
import sys
import types
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
ENTRY = '09cf0841c31394f517bc07f1c99eac4e856b8a42'
AVAILABLE = 'fbe04424e7553d9b0844ae19c2206b15cf3dd831'
ACTUAL = '5756082d85e4d6784de4566059d6a9845604342a'
DEPENDENCIES = {}


def digest(raw):
    return dict(sha256=hashlib.sha256(raw).hexdigest(), size=len(raw))


def blob(path, revision=ENTRY):
    raw = subprocess.check_output(['git', 'show', revision+':'+path], cwd=ROOT)
    DEPENDENCIES[revision+':'+path] = digest(raw)
    return raw


def module(name, path, revision=ENTRY):
    result = types.ModuleType(name)
    result.__file__ = str(ROOT/path)
    exec(compile(blob(path, revision), revision+':'+path, 'exec'), result.__dict__)
    return result


c = module('ResourceAvailable_candidate',
           'tools/resource-available-20261024/ResourceAvailable_candidate.py', AVAILABLE)
# Transparent import binding while loading unchanged GO; restored immediately.
previous = sys.modules.get(c.__name__)
sys.modules[c.__name__] = c
try:
    go = module('ResourceAvailable_go',
                'tools/resource-available-20261024/ResourceAvailable_go.py', AVAILABLE)
finally:
    if previous is None:
        sys.modules.pop(c.__name__, None)
    else:
        sys.modules[c.__name__] = previous


def original_v2_adapter():
    """Load original adapter and its unmodified sealed source loader for replay."""
    source = module('ResourceAdmit_sources',
                    'tools/resource-admit-20261024/ResourceAdmit_sources.py')
    previous_source = sys.modules.get(source.__name__)
    sys.modules[source.__name__] = source
    try:
        adapter = module('ResourceAdmit_adapter',
                         'tools/resource-admit-20261024/ResourceAdmit_adapter.py')
    finally:
        if previous_source is None:
            sys.modules.pop(source.__name__, None)
        else:
            sys.modules[source.__name__] = previous_source
    # Record all dependencies actually loaded through the original loader.
    for value in source.bundle().values():
        raw = blob(value['path'], value['revision'])
        assert digest(raw) == {k: value[k] for k in ('sha256', 'size')}
    return adapter


def fixtures():
    """Only synthetic constructors, never the unchanged historical test suite."""
    path = 'tools/resource-available-20261024/ResourceAvailable_tests.py'
    tree = ast.parse(blob(path, AVAILABLE))
    names = {'node', 'fixture', 'legacy', 'scope'}
    nodes = [n for n in tree.body if isinstance(n, ast.FunctionDef) and n.name in names]
    assert {n.name for n in nodes} == names
    env = dict(c=c, G=c.GIB)
    exec(compile(ast.Module(body=nodes, type_ignores=[]), path, 'exec'), env)
    return env
