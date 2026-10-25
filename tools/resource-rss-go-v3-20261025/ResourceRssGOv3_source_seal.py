"""Current local-only identity/import/dependency seal; no historical auditor main."""
import ast
import json
from pathlib import Path
import subprocess
import sys
import ResourceRssGOv3_host as host
import ResourceRssGOv3_local as local
import ResourceRssGOv3_sources as sources

def main():
    mapping=json.loads((local.OUT/'ResourceRssGOv3-identity.json').read_text())
    for name,record in mapping['files'].items():
        raw=subprocess.check_output(['git','show',record['revision']+':'+record['path']],cwd=local.ROOT)
        after=(local.HERE/name).read_bytes();normalized=after
        for old,new in reversed(mapping['renames']):normalized=normalized.replace(new.encode(),old.encode())
        assert host.digest(raw)==record['before'] and host.digest(after)==record['after']
        assert normalized==raw
        assert ast.dump(ast.parse(normalized),include_attributes=True)==ast.dump(ast.parse(raw),include_attributes=True)
    reviewed=sources.bundle();sources.validate_bundle(reviewed)
    dependencies={}
    for name,module in sorted(sys.modules.items()):
        path=getattr(module,'__file__',None)
        if path and Path(path).is_file() and Path(path).suffix in ('.py','.so'):
            dependencies[name]=dict(path=path,**host.filepin(path))
    historical={}
    refs=['resource-available-20261024/FAILURES.md','resource-stable-go-20261025/ResourceStableGO-FAILURES.md','resource-rss-go-20261025/ResourceRssGO-FAILURES.md','resource-rss-go-v2-20261025/ResourceRssGOv2-REPORT.md','resource-rss-go-v2-20261025/PORTABILITY-REPORT.md','resource-rss-go-v2-20261025/PORTABILITY-seal.json']
    for suffix in refs:
        path='evidence/'+suffix
        raw=subprocess.check_output(['git','show',mapping['reviewed_revision']+':'+path],cwd=local.ROOT)
        historical[path]=dict(revision=mapping['reviewed_revision'],**host.digest(raw),assessment='REUSED immutable historical reference; not rerun or a current identity gate')
    assert not any((local.OUT/name).exists() for name in ('ATTEMPTED','RUN_ATTEMPTED','runtime-inspection.json','manifest.json','marker.json'))
    bootstrap=local.inspection_payload()
    with (local.OUT/'ResourceRssGOv3-bootstrap.py.txt').open('x') as f:f.write(bootstrap+'\n')
    value=dict(status='PASS source identity/import audit; SOURCE_ONLY_BLOCKED',source_revision=local.revision(),
        dirty_overlay=subprocess.check_output(['git','status','--short','--','tools/resource-rss-go-v3-20261025','evidence/resource-rss-go-v3-20261025'],cwd=local.ROOT,text=True),
        files={p.name:host.filepin(p) for p in sorted(local.HERE.glob('*.py'))},
        identity_mapping=host.filepin(local.OUT/'ResourceRssGOv3-identity.json'),dependencies=dependencies,
        reviewed_dependencies={k:{n:v[n] for n in ('revision','path','sha256','size')} for k,v in reviewed.items()},
        historical_references=historical,bootstrap=host.digest(bootstrap.encode()),
        inherited_local_limits=host.inherited_limits(),epoch='UNUSED allocation6; five old failures unchanged',
        host_operations=0,GO=False,marker=False,axioms='N/A; no theorem/Lean execution',
        obstruction='Reviewed first inspection has no own-unit collision observation; do not introduce new operational behavior under identity-only constraint',
        both_deployed_targets='not established')
    with (local.OUT/'ResourceRssGOv3-source-seal.json').open('x') as f:json.dump(value,f,indent=2,sort_keys=True);f.write('\n')
    print('PASS normalized bytes/full AST, import closure and source-only terminal seal; host0 epoch UNUSED')

if __name__=='__main__':main()
