"""New identity seal and narrowly selected changed-identity/bootstrap checks."""
import ast
import json
from pathlib import Path
import subprocess
import sys
import unittest
import ResourceRssGOv2_local as local
import ResourceRssGOv2_host as host
import ResourceRssGOv2_sources as sources
from ResourceRssGOv2_preflight_tests import ResourceRssGOv2PreflightTests
from ResourceRssGOv2_tests import ResourceRssGOv2Tests

HERE=Path(__file__).resolve().parent
OUT=local.OUT

def main():
    mapping=json.loads((OUT/'ResourceRssGOv2-identity-mapping.json').read_text())
    for name,record in mapping['files'].items():
        after=(HERE/name).read_bytes()
        assert host.digest(after)==record['after']
        normalized=after.decode()
        for old,new in reversed(mapping['renames']):normalized=normalized.replace(new,old)
        before=(OUT/(name+'.before.py.txt')).read_bytes()
        assert normalized.encode()==before
        assert host.digest(before)==record['before']
        assert subprocess.check_output(['git','show',record['base']+':'+record['path']],cwd=local.ROOT)==before
        assert ast.dump(ast.parse(normalized),include_attributes=True)==ast.dump(ast.parse(before),include_attributes=True)
    reviewed=sources.bundle();sources.validate_bundle(reviewed)
    def suffix(raw):
        f=next(n for n in ast.parse(raw).body if isinstance(n,ast.FunctionDef) and n.name=='evaluate')
        body=next(n for n in f.body if isinstance(n,ast.Try)).body
        i=next(i for i,n in enumerate(body) if isinstance(n,ast.Assign) and isinstance(n.targets[0],ast.Name) and n.targets[0].id=='old_frontier')
        return [ast.dump(n,include_attributes=False) for n in body[i:]]
    assert suffix(reviewed['go']['source'])==suffix(reviewed['policy']['source'])
    suite=unittest.TestSuite([
        ResourceRssGOv2PreflightTests('test_exact_unstaged_payload_imports_and_limit_capture'),
        ResourceRssGOv2Tests('test_literal_env_strict_source_unit_control_and_deny'),
        ResourceRssGOv2Tests('test_changed_collector_ordered_replay'),
    ])
    result=unittest.TextTestRunner(verbosity=2).run(suite)
    assert result.wasSuccessful()
    dependencies={}
    for name,module in sorted(sys.modules.items()):
        p=getattr(module,'__file__',None)
        if p and Path(p).is_file() and Path(p).suffix in ('.py','.so'):
            dependencies[name]=dict(path=p,**host.filepin(p))
    seal=dict(source_revision=local.revision(),sources={n:host.digest(s.encode()) for n,s in local.sources().items()},
        identity_mapping=host.filepin(OUT/'ResourceRssGOv2-identity-mapping.json'),
        dependencies=dependencies,reviewed={k:{n:v[n] for n in ('revision','path','sha256','size')} for k,v in reviewed.items()},
        bootstrap_payload=host.digest(local.inspection_payload().encode()),
        normalized_byte_AST_identity=True,numerical_suffix_AST_identical=True,
        test_groups=3,axioms='N/A',epoch='UNUSED',
        reused='historical 9+8+8+5+16 groups and 14814-event audits; source assessed via immutable blobs and identity normalization, no new host identity claim',
        both_targets='not established')
    with (OUT/'ResourceRssGOv2-preparation-seal.json').open('x') as f:json.dump(seal,f,sort_keys=True,indent=2);f.write('\n')
    print('PASS identity mapping, numerical suffix, exact unstaged bootstrap and changed identity groups')
if __name__=='__main__':main()
