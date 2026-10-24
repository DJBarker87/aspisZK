"""Bounded pre-host immutable/source/argv inventory; never a live collector."""
import ast
import hashlib
import json
from pathlib import Path
import resource
import shutil
import subprocess
import sys
import time
import ResourceStableGO_sources as sources
import ResourceStableGO_host as host
import ResourceStableGO_local as local

START=time.monotonic()
ROOT=Path(__file__).resolve().parents[2]
HERE=Path(__file__).resolve().parent
OUT=ROOT/'evidence/resource-stable-go-20261025'
ENTRY='f7b90c82300c8a2409625fefb5dc529db6547f9c'

def main():
    reviewed=sources.bundle();sources.validate_bundle(reviewed)
    # Only the import names differ from the reviewed policy, whose complete bytes
    # are hard-pinned. The numerical suffix equality is rechecked as source only.
    def suffix(raw):
        f=next(n for n in ast.parse(raw).body if isinstance(n,ast.FunctionDef) and n.name=='evaluate')
        body=next(n for n in f.body if isinstance(n,ast.Try)).body
        i=next(i for i,n in enumerate(body) if isinstance(n,ast.Assign) and isinstance(n.targets[0],ast.Name) and n.targets[0].id=='old_frontier')
        return [ast.dump(n,include_attributes=False) for n in body[i:]]
    assert suffix(reviewed['go']['source'])==suffix(reviewed['policy']['source'])
    dependencies={}
    for directory in ('tools/resource-stability-20261025','tools/resource-admit-20261024'):
        names=subprocess.check_output(['git','ls-tree','-r','--name-only',ENTRY,directory],text=True).splitlines()
        for name in names:
            raw=subprocess.check_output(['git','show',ENTRY+':'+name]);dependencies[ENTRY+':'+name]=sources.digest(raw)
    for name in ('ResourceStability-POLICY.md','ResourceStability-SOURCE-ASSESSMENT.md','ResourceStability-REPORT.md','ResourceStability-terminal-seal.json'):
        p='evidence/resource-stability-20261025/'+name
        dependencies[ENTRY+':'+p]=sources.digest(subprocess.check_output(['git','show',ENTRY+':'+p]))
    # Hash old immutable packet tree names+blob IDs, without replaying old events.
    old_tree=subprocess.check_output(['git','ls-tree','-r',ENTRY,'evidence/resource-admit-20261024'])
    bundle=local.sources()
    source_pins={name:sources.digest(text.encode()) for name,text in bundle.items()}
    used_imports={}
    for name,module in sorted(sys.modules.items()):
        p=getattr(module,'__file__',None)
        if p and Path(p).is_file() and Path(p).suffix in ('.py','.so'):
            used_imports[name]=dict(path=p,**host.filepin(p))
    tools={name:dict(path=shutil.which(name),**host.filepin(shutil.which(name))) for name in ('git','ssh','ps','env')}
    result=dict(command=[sys.executable,'-B',str(Path(__file__).resolve())],source_revision=local.revision(),entry=ENTRY,
        source_pins=source_pins,reviewed_dependencies={k:{i:v[i] for i in ('revision','path','sha256','size')} for k,v in reviewed.items()},
        reviewed_sources=dependencies,local_dependencies=used_imports,tools=tools,
        old_evidence_tree=sources.digest(old_tree),historical_evidence='REUSED only, never rerun',
        literal_scope_argv=host.scope_argv(dict(env=local.env(1000))),
        numerical_suffix_AST_identical=True,public_old_apis='DISABLED',live_epoch='UNUSED',
        interpreter=dict(path=sys.executable,version=sys.version,**host.filepin(sys.executable)),exit=0,
        wall_seconds=time.monotonic()-START,peak_rss_bytes=resource.getrusage(resource.RUSAGE_SELF).ru_maxrss*(1 if sys.platform=='darwin' else 1024),
        swap=resource.getrusage(resource.RUSAGE_SELF).ru_nswap,print_axioms='N/A')
    assert result['peak_rss_bytes']<512*2**20
    with (OUT/'ResourceStableGO-preparation-seal.json').open('x') as f:json.dump(result,f,sort_keys=True,indent=2);f.write('\n')
    print(json.dumps({k:result[k] for k in ('exit','wall_seconds','peak_rss_bytes','swap','live_epoch')}))

if __name__=='__main__':main()
