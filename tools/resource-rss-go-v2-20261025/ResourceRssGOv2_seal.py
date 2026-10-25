"""Focused pre-host source seal; no historical test replay or host access."""
import ast
import json
from pathlib import Path
import subprocess
import sys
import ResourceRssGOv2_sources as sources
import ResourceRssGOv2_host as host
import ResourceRssGOv2_local as local

HERE=Path(__file__).resolve().parent
OUT=local.OUT

def main():
    reviewed=sources.bundle();sources.validate_bundle(reviewed)
    def suffix(raw):
        f=next(n for n in ast.parse(raw).body if isinstance(n,ast.FunctionDef) and n.name=='evaluate')
        body=next(n for n in f.body if isinstance(n,ast.Try)).body
        i=next(i for i,n in enumerate(body) if isinstance(n,ast.Assign) and isinstance(n.targets[0],ast.Name) and n.targets[0].id=='old_frontier')
        return [ast.dump(n,include_attributes=False) for n in body[i:]]
    assert suffix(reviewed['go']['source'])==suffix(reviewed['policy']['source'])
    diffs={}
    import difflib
    for part in ('host','local','adapter','sources','audit','receipt','fixtures'):
        old='tools/resource-stable-go-20261025/ResourceStableGO_'+part+'.py'
        before=subprocess.check_output(['git','show','4f4b0a2470:'+old],text=True)
        after=(HERE/('ResourceRssGOv2_'+part+'.py')).read_text()
        diff=''.join(difflib.unified_diff(before.splitlines(True),after.splitlines(True),fromfile='4f4b0a2470:'+old,tofile='ResourceRssGOv2_'+part+'.py'))
        (OUT/('ResourceRssGOv2-'+part+'.diff')).write_text(diff)
        diffs[part]=host.digest(diff.encode())
    deps={}
    for name,m in sorted(sys.modules.items()):
        p=getattr(m,'__file__',None)
        if p and Path(p).is_file() and Path(p).suffix in ('.py','.so'):
            deps[name]=dict(path=p,**host.filepin(p))
    result=dict(source_revision=local.revision(),entry='4f4b0a2470',
        sources={n:host.digest(s.encode()) for n,s in local.sources().items()},diffs=diffs,
        reviewed_dependencies={k:{n:v[n] for n in ('revision','path','sha256','size')} for k,v in reviewed.items()},
        local_dependencies=deps,numerical_suffix_AST_identical=True,
        inherited_limits=host.inherited_limits(),
        literal_scope_argv=host.scope_argv(dict(env=local.env(1000))),
        reused='policy8 + old8+5+16 groups and old traces; no rerun/new identity gate',
        live_epoch='UNUSED',axioms='N/A',both_security_targets='not established')
    with (OUT/'ResourceRssGOv2-preparation-seal.json').open('x') as f:json.dump(result,f,sort_keys=True,indent=2);f.write('\n')
    print(json.dumps(dict(status='PASS',numerical_suffix_AST_identical=True,live_epoch='UNUSED')))

if __name__=='__main__':main()
