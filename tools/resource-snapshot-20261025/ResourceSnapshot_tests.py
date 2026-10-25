"""Tiny offline replay only; immutable inputs; no collector/live entrypoint calls."""
import ast
import copy
import hashlib
import importlib.util
import io
import json
from pathlib import Path
import resource
import subprocess
import sys
import time
import types
import unittest

REV = 'fbe04424e7553d9b0844ae19c2206b15cf3dd831'
BASE = 'fe3e1689179edb7d1e8a9aa847aa97a3b3202360'
ROOT = Path(__file__).resolve().parents[2]
EVIDENCE = ROOT / 'evidence/resource-snapshot-20261025'


def immutable(rev, path):
    return subprocess.check_output(['git', 'show', rev+':'+path], cwd=ROOT).decode()


def module(name, source):
    result = types.ModuleType(name)
    sys.modules[name] = result
    exec(compile(source, '<immutable-offline-'+name+'>', 'exec'), result.__dict__)
    return result


start = time.monotonic()
source = Path(__file__).with_name('ResourceSnapshot_candidate.py').read_text()
c = module('ResourceAvailable_candidate', source)
predecessor = module('predecessor', immutable(BASE, 'tools/port36transport-20261025/linux367/Port36LINUX_pid_candidate.py'))
go = module('ResourceAvailable_go', immutable(REV, 'tools/resource-available-20261024/ResourceAvailable_go.py'))
generic = module('original_tests', immutable(REV, 'tools/resource-available-20261024/ResourceAvailable_tests.py'))


def capture(charged):
    s, _ = generic.scope()
    s['rows'][-1]['pids_current'] = charged
    return s


class Focused(unittest.TestCase):
    def test_staggered_captures_and_complete_memory_outputs(self):
        baseline = capture(1)
        expected = predecessor.observe(baseline)
        expected_decision = generic.evaluate(baseline)
        for charged in (2, 1, 0):
            # 1 visible <, =, > charged. Zero is a later counter read after
            # the captured task exited, not a simultaneous zero-growth claim.
            s = capture(charged)
            self.assertEqual(c.observe(s), expected)
            self.assertEqual(generic.evaluate(s), expected_decision)
            self.assertEqual(s['rows'][-1]['pids_current'], charged)
            self.assertEqual(len(s['rows'][-1]['threads']), 1)
        self.assertRaises(ValueError, predecessor.observe, capture(0))

    def test_invalid_counters_caps_and_missing_controls(self):
        for value in (-1, True, '1', 1.0, c.U64+1, None, 65):
            s = capture(1); s['rows'][-1]['pids_current'] = value
            self.assertRaises((ValueError, TypeError), c.observe, s)
        for key in ('pids_current', 'tasks_max', 'controllers', 'pids_enabled'):
            s = capture(1); del s['rows'][-1][key]
            self.assertRaises((ValueError, KeyError, TypeError), c.observe, s)
        for value in (-1, True, c.U64+1):
            s = capture(1); s['rows'][-1]['tasks_max'] = value
            self.assertRaises(ValueError, c.observe, s)

    def test_identity_membership_and_domain_failures(self):
        changes = [('threads', [42,42]), ('procs', []), ('domain', '/bad'),
                   ('identities', []), ('type', 'invalid')]
        for key,value in changes:
            s = capture(1); s['rows'][-1][key] = value
            self.assertRaises(ValueError, c.observe, s)
        s = capture(1); s['rows'][0]['threads']=[42]
        s['rows'][0]['identities']=[dict(tid=42,tgid=42,starttime=123)]
        s['rows'][0]['procs']=[42]
        self.assertRaises(ValueError, c.observe, s)
        for key,value in [('tid',43),('tgid',43),('starttime',-1)]:
            s=capture(1);s['rows'][-1]['identities'][0][key]=value
            self.assertRaises(ValueError,c.observe,s)

    def test_exact_ast_delta(self):
        original = immutable(BASE, 'tools/port36transport-20261025/linux367/Port36LINUX_pid_candidate.py')
        a = ast.parse(original); b = ast.parse(source)
        for tree in (a,b):
            tree.body = [n for n in tree.body if not (isinstance(n,ast.FunctionDef) and n.name=='validate_membership')]
        self.assertEqual(ast.dump(a), ast.dump(b))


def run_suite(case):
    stream = io.StringIO()
    result = unittest.TextTestRunner(stream=stream,verbosity=2).run(unittest.defaultTestLoader.loadTestsFromTestCase(case))
    return dict(tests=result.testsRun, failures=len(result.failures), errors=len(result.errors), successful=result.wasSuccessful(), output=stream.getvalue())


if __name__ == '__main__':
    original = run_suite(generic.ResourceAvailableTests)
    focused = run_suite(Focused)
    usage = resource.getrusage(resource.RUSAGE_SELF)
    receipt = dict(mode='source-only synthetic replay; no live collection',original16=original,focused=focused,
        exit=0 if original['successful'] and focused['successful'] else 1,
        wall_seconds=time.monotonic()-start,peak_rss_bytes=usage.ru_maxrss if sys.platform=='darwin' else usage.ru_maxrss*1024,
        swaps=usage.ru_nswap,local_limit_bytes=512*2**20,print_axioms='N/A; formal budget ZERO',
        candidate_sha256=hashlib.sha256(source.encode()).hexdigest())
    assert receipt['peak_rss_bytes'] <= receipt['local_limit_bytes']
    (EVIDENCE/'tests.json').write_text(json.dumps(receipt,indent=2)+'\n')
    print(json.dumps(receipt,indent=2))
    sys.exit(receipt['exit'])
