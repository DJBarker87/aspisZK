"""Offline audit of new local receipts only; no operational imports or host IO."""
import ast
import hashlib
import json
from pathlib import Path

OUT = Path(__file__).resolve().parent
ROOT = OUT.parents[1]
TOOLS = ROOT / 'tools/resource-rss-go-v3-20261025'

def load(name):
    return json.loads((OUT / name).read_text())

def pin(raw):
    return dict(sha256=hashlib.sha256(raw).hexdigest(), size=len(raw))

manifest = load('manifest.json')
identity = load('ResourceRssGOv3-identity.json')
seal = load('ResourceRssGOv3-source-seal.json')
for name, expected in seal['files'].items():
    assert pin((TOOLS / name).read_bytes()) == expected
for name, entry in identity['files'].items():
    assert manifest['files'][name] == entry['after']
for name, expected in manifest['files'].items():
    if name != 'ResourceRssGOv3_reviewed.json':
        assert pin((TOOLS / name).read_bytes()) == expected

inspection = load('inspect-transport.json')
stage = load('stage-transport.json')
preflight = load('stage-preflight-transport.json')
run = load('run-transport.json')
assert [x['exit'] for x in (inspection, stage, preflight, run)] == [0, 0, 0, 78]
assert all(x['source_revision'] == manifest['source_revision'] for x in (inspection, stage, preflight, run))
info = load('runtime-inspection.json')
assert json.loads(inspection['stdout']) == info
assert info['runtime'] == manifest['runtime']
assert info['inherited_limits'] == manifest['inherited_limits']
assert info['limit_platform'] == dict(platform='linux', rlim_infinity=-1)
assert info['inherited_limits']['RLIMIT_AS'] == [-1, -1]
assert info['inherited_limits']['RLIMIT_DATA'] == [-1, -1]
assert info['stage_exists'] is False and info['uid'] == info['parent_uid']
observed = json.loads(preflight['stdout'])
assert observed == {k: manifest[k] for k in ('files', 'runtime', 'env', 'mode')}
staged = json.loads(stage['stdout'])
assert staged['files'] == manifest['files'] and staged['stage'] == manifest['stage']
assert staged['uid'] == info['uid']
assert run['manifest_pin'] == pin((OUT / 'manifest.json').read_bytes())
assert run['stdout'] == run['stderr'] == ''
assert (OUT / 'ATTEMPTED').exists() and (OUT / 'RUN_ATTEMPTED').exists()
assert not (OUT / 'export-receipt.json').exists()
assert not (OUT / 'marker.json').exists()  # Local absence only, not remote absence.

# Inspect complete relevant source bodies; do not execute admission/flow fixtures.
tree = ast.parse((TOOLS / 'ResourceRssGOv3_host.py').read_text())
bodies = {n.name: ast.get_source_segment((TOOLS / 'ResourceRssGOv3_host.py').read_text(), n)
          for n in tree.body if isinstance(n, ast.FunctionDef)}
assert "terminal='PROSPECTIVE_DENY', prospective_exit=78, scope_created=False" in bodies['flow']
assert "terminal='GO_DENY', go_exit=78" in bodies['go_flow']
assert "code=0 if result.get('scope_runner_exit',78)==0 else 78" in bodies['main']
assert "stderr=(HERE/'capture/scope.stderr').open('x')" in bodies['main']
assert "stdout=(HERE/'capture/scope.stdout').open('x')" in bodies['main']
print(json.dumps(dict(status='PASS local causal audit', source_revision=manifest['source_revision'],
    observed_exits=[0, 0, 0, 78], epoch='allocation6 charged and terminal; no retry',
    established='inspection/stage/preflight succeeded against pinned maps; run returned 78',
    unresolved='prospective denial versus nonzero scope exit; remote GO/marker/controls not exported',
    host_operations_after_failure=0, admission_replay='NOT RUN: no local ordered inputs/report',
    print_axioms='N/A; no formal invocation'), sort_keys=True))
