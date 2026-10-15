import hashlib,json,subprocess,sys
from pathlib import Path
root=Path('/tmp/aspis-root-local-semantic-20261015')
repo=Path('/Users/dominic/ZK/.worktrees/100bit-spend-path')
sources=repo/'docs/research/100bit-spend-path-20261013/lean'
jobs=[('LiteralSemanticParserFacts','semantic-parser-facts-a'),('LiteralMatchingSemanticData','matching-semantic-data-a'),('LiteralOpeningPrefixFacts','opening-prefix-facts-a'),('LiteralTerminalSpend','terminal-spend-a')]
pins={target:hashlib.sha256((sources/(target+'.lean')).read_bytes()).hexdigest() for target,_ in jobs}
(root/'composition-queue-source-pins.json').write_text(json.dumps(pins,indent=2)+'\n')
for target,label in jobs:
    assert hashlib.sha256((sources/(target+'.lean')).read_bytes()).hexdigest()==pins[target], 'queued source changed: '+target
    print('START '+target+' '+label,flush=True)
    with (root/'attempts'/(label+'.time.log')).open('x') as timing:
        ret=subprocess.run(['/usr/bin/time','-l','python3',str(root/'run-next.py'),target,label],stderr=timing).returncode
    print('END '+target+' exit='+str(ret),flush=True)
    if ret: sys.exit(ret)
