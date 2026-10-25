from pathlib import Path
import subprocess,hashlib,json
root=Path.cwd();t=root/'tools/resource-stable-go-20261025';e=root/'evidence/resource-stable-go-20261025'
def blob(p,r='f7b90c82300c8a2409625fefb5dc529db6547f9c'):return subprocess.check_output(['git','show',r+':'+p])
def old(n):return blob('tools/resource-admit-20261024/ResourceAdmit_'+n+'.py').decode()
def translated(s):return s.replace('ResourceAdmit','ResourceStableGO').replace('resource-admit-20261024/v2','resource-stable-go-20261025').replace('codex-cx-resource-admit-20261025-v2','codex-cx-resource-stable-go-20261025').replace('resource-admit-20261025-v2','resource-stable-go-20261025').replace('ResourceStableGO-20261025-v2','ResourceStableGO-20261025-epoch1').replace('ResourceStableGO20261025-v2','ResourceStableGO20261025-v1')
s=old('sources').replace('ResourceAdmit','ResourceStableGO')
s=s.replace("    'fixtures':", "    'policy':('stability','tools/resource-stability-20261025/ResourceStability_evaluator.py'),\n    'fixtures':")
s=s.replace("REVISIONS = {", "REVISIONS = {'stability':'f7b90c82300c8a2409625fefb5dc529db6547f9c',")
# hardcoded reviewed bytes validated on BOTH git and staged paths, before execution.
s=s.replace("def load_bundle():", "def load_bundle():")
s=s.replace("    return data\n\ndef functions", "    validate_bundle(data)\n    return data\n\ndef functions")
s=s.replace("    candidate=types.ModuleType", "    validate_bundle(data)\n    candidate=types.ModuleType")
s=s.replace("    return candidate,go,identity,inventory", """    aliases=types.ModuleType('ResourceStability_sources')
    aliases.c=candidate
    aliases.go=types.SimpleNamespace(**go)
    previous=sys.modules.get('ResourceStability_sources')
    sys.modules['ResourceStability_sources']=aliases
    try:
        policy=types.ModuleType('ResourceStableGO_reviewed_policy')
        exec(compile(data['policy']['source'],data['policy']['path'],'exec'),policy.__dict__)
    finally:
        if previous is None:sys.modules.pop('ResourceStability_sources',None)
        else:sys.modules['ResourceStability_sources']=previous
    return candidate,go,identity,inventory,policy""")
specs={
'candidate':('fbe04424e7553d9b0844ae19c2206b15cf3dd831','tools/resource-available-20261024/ResourceAvailable_candidate.py'),
'go':('fbe04424e7553d9b0844ae19c2206b15cf3dd831','tools/resource-available-20261024/ResourceAvailable_go.py'),
'identity':('5756082d85e4d6784de4566059d6a9845604342a','tools/resource-stat-20261024/ResourceStat_go.py'),
'inventory':('5756082d85e4d6784de4566059d6a9845604342a','tools/resource-stat-20261024/baseline/reservation_base.py'),
'fixtures':('fbe04424e7553d9b0844ae19c2206b15cf3dd831','tools/resource-available-20261024/ResourceAvailable_tests.py'),
'policy':('f7b90c82300c8a2409625fefb5dc529db6547f9c','tools/resource-stability-20261025/ResourceStability_evaluator.py')}
pins={k:dict(sha256=hashlib.sha256(blob(p,r)).hexdigest(),size=len(blob(p,r))) for k,(r,p) in specs.items()}
s+='\nPINS = '+repr(pins)+'''

def validate_bundle(data):
    if set(data)!=set(SPECS):raise ValueError('reviewed source set drift')
    for key,(rev,path) in SPECS.items():
        item=data[key]
        if item['revision']!=REVISIONS[rev] or item['path']!=path or digest(item['source'].encode())!=PINS[key] or {k:item[k] for k in ('sha256','size')}!=PINS[key]:
            raise ValueError('reviewed immutable source pin drift: '+key)
'''
(t/'ResourceStableGO_sources.py').write_text(s)
s=translated(old('adapter')).replace('Pure reviewed evaluator remains unchanged.','Reviewed ResourceStability policy used for one explicitly allocated epoch only.')
s=s.replace('c, go, identity, inventory = load()','c, go, identity, inventory, policy = load()')
start=s.index("    decision=go['evaluate']")
end=s.index('    if failures:decision.update',start)
s=s[:start]+'''    decision=policy.evaluate(old,snapshots['before'],snapshots['after'],requested,phase=phase,
        expected=EXPECTED if phase=='inside-scope' else None,
        expected_unit=UNIT+'.scope' if phase=='inside-scope' else None)
'''+s[end:]
(t/'ResourceStableGO_adapter.py').write_text(s)
s=translated(old('host')).replace("MODE = 'limited ResourceAvailable policy; metadata-only; no consumer'", "MODE = 'limited ResourceStability20261025-v1 policy; one metadata epoch only; no consumer'")
s=s.replace("epoch 2/2", "new epoch 1/1; prior two epochs remain charged failures")
s=s.replace('import ResourceStableGO_adapter as adapter', "if sys.platform == 'linux':\n    resource.setrlimit(resource.RLIMIT_AS,(512*2**20,512*2**20))\nimport ResourceStableGO_adapter as adapter")
# post-marker controls and pins checked, marker identity binding stronger raw self receipt.
s=s.replace("identity='ResourceStableGO metadata marker only'", "identity='ResourceStableGO metadata marker only',self_observation=adapter.identity['self_observation'](),go_report_pin=filepin(HERE/'capture/inside-scope-report.json'),source_manifest_pin=filepin(HERE/'ResourceStableGO_manifest.json')")
s=s.replace("        save('go-controls-after.json',controls())", "        final_controls=controls()\n        save('go-controls-after.json',final_controls)\n        check_controls(final_controls)")
(t/'ResourceStableGO_host.py').write_text(s)
s=translated(old('local'))
start=s.index('def coordination():');end=s.index('\n\ndef save(',start)
s=s[:start]+'''COORD_OUTPUT=Path('/private/tmp/claude-501/-Users-dominic-ZK/4dec4925-8c43-447e-9333-6147c1c7863b/scratchpad/codex-sbf-closure-20261025.out')
def coordination():
    observed=subprocess.run(['ps','-p','18006','-o','pid=,lstart=,command='],text=True,capture_output=True)
    if observed.returncode!=1 or observed.stdout.strip():raise RuntimeError('WAITING: coordination PID present or inspection failed')
    raw=COORD_OUTPUT.read_bytes()
    if not raw.splitlines() or raw.splitlines()[-1]!=b'codex-exit=0':raise RuntimeError('WAITING: exact terminal marker missing')
    return dict(pid=18006,ps_exit=observed.returncode,ps_stdout=observed.stdout,terminal='codex-exit=0',output_pin=host.digest(raw),host0='Port29SDKDATA21361 LOCALONLY')

def charge():
    coordination()
    with (OUT/'ATTEMPTED').open('x') as f:f.write(host.EPOCH+'; new epoch1/1; prior two failures retained; charged before first SSH including transport failure\\n')

''' +s[end:]
s=s.replace('def inspect():\n', 'def inspect():\n    charge()\n')
s=s.replace("(OUT/'ATTEMPTED').open('x').close()", "assert (OUT/'ATTEMPTED').exists(), 'epoch not charged before host preparation'\n    (OUT/'RUN_ATTEMPTED').open('x').close()")
s=s.replace("peak_rss_bytes=usage.ru_maxrss if platform.system()=='Darwin' else usage.ru_maxrss*1024", "peak_rss_bytes=usage.ru_maxrss if platform.system()=='Darwin' else usage.ru_maxrss*1024")
s=s.replace("def export():", '''def preflight():
    manifest=json.loads((OUT/'manifest.json').read_text())
    payload="import sys,json;sys.path.insert(0,"+repr(REMOTE)+");import ResourceStableGO_host as h;m=json.loads((h.HERE/'ResourceStableGO_manifest.json').read_text());print(json.dumps(h.verify(m),sort_keys=True))"
    result=ssh_python(payload,'stage-preflight',environment=manifest['env'])
    if result.returncode:raise RuntimeError('preflight failure terminal; no retry')

def export():''')
s=s.replace("'stage','run','export'", "'stage','preflight','run','export'")
# transport metrics explicitly N/A
s=s.replace("print_axioms='N/A'", "peak_rss_bytes='N/A unmeasured SSH transport',swap='N/A unmeasured SSH transport',print_axioms='N/A'")
# above indiscriminate metrics duplicate in tests() keywords? only tests print_axioms has preceding peak_rss; will fix
s=s.replace("log_pin=host.filepin(OUT/(label+'.log')),peak_rss_bytes='N/A unmeasured SSH transport',swap='N/A unmeasured SSH transport',print_axioms", "log_pin=host.filepin(OUT/(label+'.log')),print_axioms")
(t/'ResourceStableGO_local.py').write_text(s)
s=translated(old('audit'))
s=s.replace("assert load('marker.json')['pid']==binding['pid']", """assert load('marker.json')['pid']==binding['pid']
        marker=load('marker.json')
        assert {k:v for k,v in marker['self_observation'].items() if k!='reads'}==binding
        assert marker['go_report_pin']=={k:export['host_files']['inside-scope-report.json'][k] for k in ('sha256','size')}
        assert marker['source_manifest_pin']==host.filepin(OUT/'manifest.json')""")
(t/'ResourceStableGO_audit.py').write_text(s)
# exact historical receipt utility adapted only names/paths
s=blob('tools/resource-stability-20261025/ResourceStability_receipt.py').decode().replace('ResourceStability','ResourceStableGO').replace('resource-stability-20261025','resource-stable-go-20261025')
s=s.replace("with (OUT/(label+'.log')).open('wb')", "with (OUT/(label+'.log')).open('xb')").replace("(OUT/(label+'-receipt.json')).write_text(json.dumps(receipt,sort_keys=True,indent=2)+'\\n')", "with (OUT/(label+'-receipt.json')).open('x') as f:f.write(json.dumps(receipt,sort_keys=True,indent=2)+'\\n')")
(t/'ResourceStableGO_receipt.py').write_text(s)
# standalone reusable fixture functions only from old tests (not suite).
import ast
oldtree=ast.parse(old('tests'))
names={'fixture','virtual','kernel'}
selected=[n for n in oldtree.body if isinstance(n,ast.FunctionDef) and n.name in names]
fixture_text='''"""Reused immutable synthetic kernel constructors; no historical test suite."""
import contextlib
import os
from pathlib import Path
import subprocess
from types import SimpleNamespace
from unittest.mock import patch
import ResourceStableGO_adapter as a
from ResourceStableGO_sources import functions,load_bundle
fixtures=functions(load_bundle()['fixtures']['source'],['node','fixture','scope'],dict(c=a.c,G=a.c.GIB))
'''+translated(ast.unparse(ast.Module(body=selected,type_ignores=[])))+'\n'
(t/'ResourceStableGO_fixtures.py').write_text(fixture_text)
# source diffs precise adapter/host/local/audit/source vs old
import difflib
for n in ('adapter','host','local','audit','sources'):
 (e/('ResourceStableGO-'+n+'.diff')).write_text(''.join(difflib.unified_diff(old(n).splitlines(True),(t/('ResourceStableGO_'+n+'.py')).read_text().splitlines(True),fromfile='f7b90c8230:ResourceAdmit_'+n+'.py',tofile='ResourceStableGO_'+n+'.py')))
(e/'ResourceStableGO-reviewed-dependencies.json').write_text(json.dumps({k:dict(revision=r,path=p,**pins[k]) for k,(r,p) in specs.items()},indent=2,sort_keys=True)+'\n')
