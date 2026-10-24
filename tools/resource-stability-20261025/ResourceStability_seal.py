"""Final bounded file/source seal. Does not repeat tests or historical replay."""
import hashlib
import json
import resource
import subprocess
import sys
import time
from pathlib import Path

START=time.monotonic()
ROOT=Path(__file__).resolve().parents[2]
TOOLS=ROOT/'tools/resource-stability-20261025'
OUT=ROOT/'evidence/resource-stability-20261025'
ENTRY='09cf0841c31394f517bc07f1c99eac4e856b8a42'


def pin(raw):return dict(sha256=hashlib.sha256(raw).hexdigest(),size=len(raw))


def main():
    revision=subprocess.check_output(['git','rev-parse','HEAD'],cwd=ROOT,text=True).strip()
    changed=subprocess.check_output(['git','diff','--name-only',ENTRY],cwd=ROOT,text=True).splitlines()
    assert all(p.startswith(('tools/resource-stability-20261025/','evidence/resource-stability-20261025/')) for p in changed)
    source_binding={}
    for label in ('focused-third','audit-third'):
        r=json.loads((OUT/(label+'-receipt.json')).read_bytes())
        assert r['exit']==0 and r['peak_rss_bytes']<512*2**20 and r['swap']==0
        assert pin((OUT/(label+'.log')).read_bytes())==r['output']
        for name,value in r['sources'].items():
            raw=subprocess.check_output(['git','show',revision+':tools/resource-stability-20261025/'+name],cwd=ROOT)
            assert pin(raw)==value==pin((TOOLS/name).read_bytes()),('source changed',label,name)
        source_binding[label]=dict(receipt=pin((OUT/(label+'-receipt.json')).read_bytes()),
            execution_revision=r['source_revision'],matching_committed_source_revision=revision,
            exact_source_hashes=r['sources'])
    audit=json.loads((OUT/'ResourceStability-audit.json').read_bytes())
    assert audit['original_v2_replay']['events']==14926
    assert audit['original_v2_replay']['original_allowed'] is False
    assert audit['v2_counterfactual']['new_policy']['allowed'] is True
    assert audit['live_API']=='DISABLED' and audit['adopted'] is False
    files={str(p.relative_to(ROOT)):pin(p.read_bytes()) for directory in (TOOLS,OUT)
        for p in sorted(directory.iterdir()) if p.is_file() and p.name!='ResourceStability-terminal-seal.json'}
    assert all(p['size']<=5_000_000 for p in files.values())
    usage=resource.getrusage(resource.RUSAGE_SELF)
    result=dict(command=[sys.executable,'-B',str(Path(__file__).resolve())],exit=0,
        wall_seconds=time.monotonic()-START,
        peak_rss_bytes=usage.ru_maxrss*(1 if sys.platform=='darwin' else 1024),
        swap=usage.ru_nswap,source_revision=revision,entry_revision=ENTRY,
        interpreter=dict(path=sys.executable,version=sys.version,**pin(Path(sys.executable).read_bytes())),
        sources_and_evidence=files,source_binding=source_binding,
        immutable_inputs_and_dependencies='ResourceStability-dependencies.json',
        host_operations=0,live_API='DISABLED',adopted=False,
        print_axioms='N/A; no Lean/native/security obligations discharged',
        both_security_targets='not established',Kani='59/60; final gate reserved',
        whitespace_check='unified diff context blank lines contain required single-space markers; no source whitespace change')
    assert result['peak_rss_bytes']<512*2**20
    (OUT/'ResourceStability-terminal-seal.json').write_text(json.dumps(result,sort_keys=True,indent=2)+'\n')
    print(json.dumps({k:result[k] for k in ('exit','source_revision','wall_seconds','peak_rss_bytes','swap','live_API')},sort_keys=True))


if __name__=='__main__':main()
