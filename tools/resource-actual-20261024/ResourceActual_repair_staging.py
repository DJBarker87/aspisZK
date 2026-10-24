"""Single exact repair for recorded malformed staging manifest, before live attempt.

Preserve original bytes; no operational source changes, scope, or live API call.
"""
import json
from pathlib import Path
import ResourceActual_local as local


def main():
    assert not (local.OUT/'ATTEMPTED').exists()
    manifest=json.loads((local.OUT/'manifest.json').read_text())
    payload="""import hashlib,json,os,pathlib,sys
root=pathlib.Path(REMOTE)
manifest=json.load(sys.stdin)
p=root/'manifest.json'; raw=p.read_bytes()
expected=json.dumps(manifest,sort_keys=True,indent=2).encode()
assert raw==expected+bytes([92,110]), 'not the recorded staging failure'
backup=root/'staging-malformed-manifest.raw'
with backup.open('xb') as f:f.write(raw)
backup.chmod(0o444)
p.chmod(0o600)
p.write_bytes(expected+bytes([10]))
p.chmod(0o444)
assert json.loads(p.read_text())==manifest
ns={'__file__':str(root/'ResourceActual_host.py'),'__name__':'repair_preflight'}
exec(compile((root/'ResourceActual_host.py').read_text(),ns['__file__'],'exec'),ns)
pins=ns['verify'](manifest)
print(json.dumps(dict(original_pin=ns['digest'](raw),corrected_pin=ns['filepin'](p),preflight=pins)))
""".replace('REMOTE',repr(local.REMOTE))
    result=local.ssh_python(payload,'repair-staging',environment=manifest['env'],data=json.dumps(manifest))
    assert result.returncode==0,'repair/preflight failed: no live attempt permitted'

if __name__=='__main__':main()
