"""Read only retained local frame shards, reconstruct exact capture bytes."""
import base64,hashlib,json
from pathlib import Path
OUT=Path(__file__).resolve().parents[2]/'evidence/resource-rss-go-v3-20261025'
def raw(name):
    result=bytearray();expected=None
    for path in sorted(OUT.glob('EVIDENCE-frames-*.jsonl')):
        for line in path.open('rb'):
            obj=json.loads(line)
            if obj.get('name')!=name:continue
            if obj['kind']=='chunk':result.extend(base64.b64decode(obj['data'],validate=True))
            elif obj['kind']=='end':expected=obj
            elif obj['kind']=='absent':raise FileNotFoundError(name)
    assert expected and len(result)==expected['size'] and hashlib.sha256(result).hexdigest()==expected['sha256']
    return bytes(result)
def load(name):return json.loads(raw(name))
if __name__=='__main__':
    for name in ['run-exit.json','go-exit.json','scope-child.json','scope.stderr','go-control-check.json','prospective-metrics.json','inside-scope-metrics.json']:
        print(name,raw(name).decode())
    for phase in ('prospective','inside-scope'):
        report=load(phase+'-report.json');d=report['decision']
        print(phase,json.dumps({k:v for k,v in d.items() if k not in ('legacy','before_observation','after_observation','membership_differences')},sort_keys=True))
