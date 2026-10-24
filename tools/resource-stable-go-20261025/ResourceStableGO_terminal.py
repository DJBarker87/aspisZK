"""Final file/source binding only; no repeated replay, test, or host operation."""
import json
from pathlib import Path
import resource
import subprocess
import sys
import time
import ResourceStableGO_sources as sources
import ResourceStableGO_host as host

START=time.monotonic()
ROOT=Path(__file__).resolve().parents[2]
HERE=Path(__file__).resolve().parent
OUT=ROOT/'evidence/resource-stable-go-20261025'
ENTRY='f7b90c82300c8a2409625fefb5dc529db6547f9c'

def load(name):return json.loads((OUT/name).read_bytes())

def main():
    revision=subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip()
    changed=subprocess.check_output(['git','diff','--name-only',ENTRY],text=True).splitlines()
    assert all(p.startswith(('tools/resource-stable-go-20261025/','evidence/resource-stable-go-20261025/')) for p in changed)
    manifest=load('manifest.json');source_bindings={}
    for name,pin in manifest['files'].items():
        raw=(json.dumps(sources.bundle(),sort_keys=True,indent=2)+'\n').encode() if name=='ResourceStableGO_reviewed.json' else (HERE/name).read_bytes()
        assert host.digest(raw)==pin
        if name!='ResourceStableGO_reviewed.json':
            assert host.digest(subprocess.check_output(['git','show',manifest['source_revision']+':tools/resource-stable-go-20261025/'+name]))==pin
        source_bindings[name]=pin
    receipts={}
    for label in ('focused-first','actual-audit-first','failure-assessment'):
        r=load(label+'-receipt.json');assert r['exit']==0 and r['swap']==0 and r['peak_rss_bytes']<512*2**20
        assert r['output']==host.filepin(OUT/(label+'.log'))
        for name,pin in r['sources'].items():assert host.filepin(HERE/name)==pin
        receipts[label]=dict(receipt_pin=host.filepin(OUT/(label+'-receipt.json')),matching_sources=True,execution_revision=r['source_revision'])
    for name in ('run-pre-pins.json','run-post-pins.json'):
        pins=load(name)
        for key in ('files','runtime','env'):assert pins[key]==manifest[key]
    for label in ('inspect','stage','stage-preflight'):
        assert load(label+'-transport.json')['exit']==0
    assert load('run-transport.json')['exit']==78
    result=load('run-exit.json');assert result['terminal']=='PROSPECTIVE_DENY' and result['scope_created'] is False
    assert (OUT/'ATTEMPTED').exists() and (OUT/'RUN_ATTEMPTED').exists()
    assert not any((OUT/name).exists() for name in ('scope-argv.json','scope-child.json','marker.json','go-pre-pins.json'))
    files={str(p.relative_to(ROOT)):host.filepin(p) for d in (HERE,OUT) for p in sorted(d.iterdir()) if p.is_file() and p.name!='ResourceStableGO-terminal-seal.json'}
    assert all(v['size']<=5_000_000 for v in files.values())
    packet=dict(command=[sys.executable,'-B',str(Path(__file__).resolve())],source_revision=revision,entry=ENTRY,
        source_bindings=source_bindings,receipts=receipts,files=files,
        interpreter=dict(path=sys.executable,version=sys.version,**host.filepin(sys.executable)),
        terminal='PROSPECTIVE_DENY',new_epoch='USED1/1',actual_scope='unused; no residual epoch authority',actual_GO=False,marker=False,
        historical_failures='retained byte-identical in immutable entry; no recertification',
        old_evidence_tree=host.digest(subprocess.check_output(['git','ls-tree','-r',ENTRY,'evidence/resource-admit-20261024'])),
        print_axioms='N/A',both_security_targets='not established',Kani='59/60 final RESERVED',
        exit=0,wall_seconds=time.monotonic()-START,peak_rss_bytes=resource.getrusage(resource.RUSAGE_SELF).ru_maxrss*(1 if sys.platform=='darwin' else 1024),swap=resource.getrusage(resource.RUSAGE_SELF).ru_nswap)
    assert packet['peak_rss_bytes']<512*2**20
    with (OUT/'ResourceStableGO-terminal-seal.json').open('x') as f:json.dump(packet,f,indent=2,sort_keys=True);f.write('\n')
    print(json.dumps({k:packet[k] for k in ('exit','terminal','new_epoch','wall_seconds','peak_rss_bytes','swap')}))

if __name__=='__main__':main()
