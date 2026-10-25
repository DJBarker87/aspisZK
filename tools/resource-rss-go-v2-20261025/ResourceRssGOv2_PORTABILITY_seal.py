"""Source-only portability delta audit/seal; no operational entry points."""
import ast
import difflib
import hashlib
import json
from pathlib import Path
import subprocess
import sys
# Importing the focused module captures its Python dependency closure; tests are
# NOT replayed here. No Linux runtime inventory is imported or executed as main.
import ResourceRssGOv2_PORTABILITY_tests as tests

BASE='468619b15180119560c138c83127da58ba3b4c23'
ROOT=Path(__file__).resolve().parents[2]
HERE=Path(__file__).resolve().parent
OUT=ROOT/'evidence/resource-rss-go-v2-20261025'
PREFIX=str(HERE.relative_to(ROOT))
EPREFIX=str(OUT.relative_to(ROOT))


def git(*args):
    return subprocess.check_output(['git',*args],cwd=ROOT)


def pin(raw):
    return dict(sha256=hashlib.sha256(raw).hexdigest(),size=len(raw))


def save(name,raw):
    with (OUT/name).open('xb') as f:f.write(raw)
    return pin(raw)


def main():
    revision=git('rev-parse','HEAD').decode().strip()
    dirty=git('status','--porcelain=v1','--untracked-files=all').decode()
    mapping=json.loads((OUT/'ResourceRssGOv2-identity-mapping.json').read_text())
    assert len(mapping['files'])==12
    modules={}
    for name,record in sorted(mapping['files'].items()):
        old=git('show',BASE+':'+PREFIX+'/'+name)
        new=(HERE/name).read_bytes()
        assert pin(old)==record['after']
        if name!='ResourceRssGOv2_local.py':assert new==old,name
        modules[name]=dict(base=pin(old),current=pin(new),unchanged=old==new)
    assert sum(not v['unchanged'] for v in modules.values())==1
    historical={}
    for path in git('ls-tree','-r','--name-only',BASE,'--',EPREFIX).decode().splitlines():
        old=git('show',BASE+':'+path);new=(ROOT/path).read_bytes()
        assert old==new,path
        historical[path]=pin(new)
    path=PREFIX+'/ResourceRssGOv2_local.py'
    old=git('show',BASE+':'+path).decode();new=(ROOT/path).read_text()
    def nodes(source):
        return {n.name:ast.dump(n,include_attributes=False) for n in ast.parse(source).body if isinstance(n,ast.FunctionDef)}
    before,after=nodes(old),nodes(new)
    changed={name:dict(before=before.get(name),after=after.get(name)) for name in sorted(set(before)|set(after)) if before.get(name)!=after.get(name)}
    assert set(changed)=={'inspection_payload','check_remote_linux_limits','inspect','stage'}
    def top(source):
        return [ast.dump(n,include_attributes=False) for n in ast.parse(source).body if not isinstance(n,ast.FunctionDef)]
    assert top(old)==top(new)
    patch=''.join(difflib.unified_diff(old.splitlines(True),new.splitlines(True),fromfile=BASE+'/'+path,tofile=revision+'/'+path))
    artifacts={}
    for name,raw in (
        ('PORTABILITY-local-before.py.txt',old.encode()),
        ('PORTABILITY-local-after.py.txt',new.encode()),
        ('PORTABILITY-source.diff',patch.encode()),
        ('PORTABILITY-AST-diff.json',(json.dumps(changed,indent=2,sort_keys=True)+'\n').encode()),
        ('PORTABILITY-bootstrap.py.txt',tests.local.inspection_payload().encode())):
        artifacts[name]=save(name,raw)
    # Fixed mapping source evidence is read-only local SDK source and immutable
    # Linux Python capture. No external docs fetched, no Linux inventory run.
    sdk=Path('/Library/Developer/CommandLineTools/SDKs/MacOSX.sdk/usr/include/sys/resource.h')
    sdkraw=sdk.read_bytes()
    definition=next(line for line in sdkraw.decode().splitlines() if line.startswith('#define RLIM_INFINITY'))
    assert '(((__uint64_t)1 << 63) - 1)' in definition
    assert tests.resource.RLIM_INFINITY==9223372036854775807
    captured=tests.retained()['inherited_limits']
    assert captured['RLIMIT_AS']==captured['RLIMIT_DATA']==[-1,-1]
    dependencies={}
    for name,module in sorted(sys.modules.items()):
        value=getattr(module,'__file__',None)
        if value and Path(value).is_file():
            dependencies[name]=dict(path=str(Path(value).resolve()),**pin(Path(value).read_bytes()))
    receipts={}
    for name in ('PORTABILITY-focused-receipt.json','PORTABILITY-predicate-focused-receipt.json'):
        receipt=json.loads((OUT/name).read_text());assert receipt['exit']==0 and receipt['swap']==0
        receipts[name]=dict(pin=pin((OUT/name).read_bytes()),result=receipt)
    changed_paths=git('diff','--name-only',BASE,'--').decode().splitlines()
    assert all(p.startswith(PREFIX+'/') or p.startswith(EPREFIX+'/') for p in changed_paths)
    result=dict(status='PASS source-only PORTABILITY audit; not operational approval',
        base_revision=BASE,source_revision=revision,dirty_state_at_seal=dirty,
        sources={p.name:pin(p.read_bytes()) for p in sorted(HERE.glob('*.py'))},
        reviewed_twelve_modules=modules,unchanged_historical_evidence=historical,
        exact_delta_artifacts=artifacts,focused_tests=receipts,dependencies=dependencies,
        interpreter=dict(path=sys.executable,version=sys.version,**pin(Path(sys.executable).read_bytes())),
        fixed_mapping_justification=dict(local_source=dict(path=str(sdk),definition=definition,**pin(sdkraw)),
            darwin_python_infinity=tests.resource.RLIM_INFINITY,linux_python_wire_infinity=-1,
            linux_evidence='immutable pin-attested runtime-inspection.json and inspect-transport.json; empirical capture, not new host validation',
            enforcement='new exact bootstrap platform/infinity predicate and fixed local metadata schema; no caller-selected sentinel'),
        local_callsite_assessment=dict(inspect='explicit remote Linux wire validator',stage='same validator before manifest/source packaging',
            host='all same-platform verify/main/final checks remain byte-identical and use LOCAL resource constant',
            seal='historical local inherited limits are local observations only',
            receipt='Darwin RSS bytes / Linux KiB selection retained',
            old_preparation_failure_audits='historical source-specific programs, unchanged; not re-executed against new identity'),
        retained=dict(numeric_maps='unchanged, no normalization',whole_map_comparator='exact equality retained in host and remote validator',
            guard_policy_environment_controls_lifecycle='11/12 mapped modules byte-identical; local unrelated AST unchanged',
            security_trust_premises='none added/removed/changed; no formal claim'),
        next_future_argv=[sys.executable,'-B',PREFIX+'/ResourceRssGOv2_local.py','inspect'],
        future_argv_authorized=False,future_requirements='independent lead review, separate new epoch, explicit copy/identity delta accounting; old preparation_check/mapping/seals cannot attest new source',
        actual_operations=dict(SSH=0,host=0,network=0,stage=0,preflight=0,run=0,export=0,GO=0,marker=0,compiler=0,Lean=0,native=0,ELF=0),
        epoch='USED1/1; all FIVE earlier metadata epochs remain FAILED/charged; no reset',
        print_axioms='N/A; no formal theorem or Lean execution',Kani='59/60 final RESERVED',both_deployed_targets='not established')
    save('PORTABILITY-seal.json',(json.dumps(result,indent=2,sort_keys=True)+'\n').encode())
    print(json.dumps(dict(status=result['status'],unchanged_mapped_modules=11,changed_functions=sorted(changed),historical_files_unchanged=len(historical),test_groups=6,SSH=0,axioms='N/A'),sort_keys=True))

if __name__=='__main__':main()
