"""LOCAL finite source preparation only. Creates a fresh prospective DATA overlay.
No transfer/setup/host calls. Never imports or executes the prospective payload.
"""
import ast
import base64
import difflib
import hashlib
import json
from pathlib import Path

D=Path(__file__).resolve().parent
RELEASE=D/'prospective-data-v6'
STAGE='/home/dombarker/final-native-gate-v6-20261025/'
ENTRY='018e9d2aff669c3b1292e3ad49dfdc9a7d605620'

def pin(raw):return dict(size=len(raw),sha256=hashlib.sha256(raw).hexdigest())
def dump(value):return (json.dumps(value,sort_keys=True,indent=2)+'\n').encode()
def funcs(raw):
    return {n.name:ast.dump(n,include_attributes=False) for n in ast.parse(raw).body if isinstance(n,(ast.FunctionDef,ast.ClassDef))}

def prepare(release=None):
    release=RELEASE if release is None else Path(release)
    release.mkdir(mode=0o700,exist_ok=False)
    source={p.name:p.read_bytes() for p in sorted(D.iterdir()) if p.is_file()}
    rows=dict(source);delta={};diff=[]
    # Two literal setup-only entry changes. Isolated Python requires fixed path
    # bootstrap before importing sibling source, even in the outer setup entry.
    replacements={
      'FinalNativeGate_setup.py':("def main():\n    print('FinalNativeGate setup source-only: disabled; review and new allocation required')\n    return 78", "def main():\n    import sys\n    if HERE!=STAGE:raise ValueError('wrong fixed DATA stage')\n    sys.path.insert(0,str(STAGE))\n    return _prospective()"),
      'FinalNativeGate_setup_inside.py':("def main():\n    print('FinalNativeGate setup inside source-only: disabled')\n    return 78", "def main():\n    return _bound_body()")}
    for name,(before,after) in replacements.items():
        text=rows[name].decode()
        if text.count(before)!=1:raise ValueError('entry before statement mismatch: '+name)
        rows[name]=text.replace(before,after).encode()
        delta[name]=dict(before=before,after=after,before_pin=pin(source[name]),after_pin=pin(rows[name]))
        diff.extend(difflib.unified_diff(text.splitlines(True),rows[name].decode().splitlines(True),fromfile='disabled/'+name,tofile='prospective-DATA/'+name))
    p=json.loads(rows['FinalNativeGate-plan.json'])
    for path in list(p['files']):
        if path.startswith(STAGE):del p['files'][path]
    p['job_source_sizes']={}
    for name,raw in sorted(rows.items()):
        if name.endswith('.py') and name not in ('FinalNativeGate_seal.py','FinalNativeGate_bootstrap_seal.py'):
            p['files'][STAGE+name]=pin(raw)['sha256'];p['job_source_sizes'][STAGE+name]=len(raw)
    p['job_revision']=ENTRY+' plus prospective-data-v6 exact transfer-manifest overlay (activated DATA bytes only)'
    p['setup_catalog_roots']=sorted(set(p['native_roots'])|set(p['files']))
    rows['FinalNativeGate-plan.json']=dump(p)
    rows['FinalNativeGate_seal.py']=('PLAN_SHA256 = '+repr(pin(rows['FinalNativeGate-plan.json'])['sha256'])+'\n').encode()
    bootstrap={n:pin(raw) for n,raw in sorted(rows.items()) if n not in ('FinalNativeGate-bootstrap.json','FinalNativeGate_bootstrap_seal.py')}
    rows['FinalNativeGate-bootstrap.json']=dump(bootstrap)
    rows['FinalNativeGate_bootstrap_seal.py']=('BOOTSTRAP_SHA256 = '+repr(pin(rows['FinalNativeGate-bootstrap.json'])['sha256'])+'\n').encode()
    manifest={name:pin(raw) for name,raw in sorted(rows.items())}
    identities={name:dict(unchanged=sorted(k for k,v in funcs(raw).items() if funcs(rows[name]).get(k)==v),
                        changed=sorted(k for k,v in funcs(raw).items() if funcs(rows[name]).get(k)!=v))
                for name,raw in source.items() if name.endswith('.py')}
    changed=sorted(name for name in rows if rows[name]!=source[name])
    assert changed==sorted([*replacements,'FinalNativeGate-plan.json','FinalNativeGate_seal.py','FinalNativeGate-bootstrap.json','FinalNativeGate_bootstrap_seal.py'])
    assert all(v['changed']==(['main'] if n in replacements else []) for n,v in identities.items())
    for name in ('FinalNativeGate.py','FinalNativeGate_inside.py'):
        assert rows[name]==source[name]
    payload=release/'payload';payload.mkdir(mode=0o700)
    for name,raw in rows.items():
        with (payload/name).open('xb') as f:f.write(raw)
    encoded={name:dict(**manifest[name],b85=base64.b85encode(raw).decode()) for name,raw in sorted(rows.items())}
    root=hashlib.sha256(json.dumps(manifest,sort_keys=True).encode()).hexdigest()
    receiver=source['FinalNativeGate-transfer-template.txt'].decode().replace('__FILES_LITERAL__',repr(encoded)).replace('__ROOT_LITERAL__',repr(root)).encode()
    assert len(receiver)<4*2**20
    with (release/'FinalNativeGate-data-transfer.py').open('xb') as f:f.write(receiver)
    transport=source['FinalNativeGate-transport-template.txt'].decode().replace('__RECEIVER_PIN__',repr(pin(receiver))).encode()
    with (release/'FinalNativeGate-data-transport.py').open('xb') as f:f.write(transport)
    report=dict(transport=pin(transport),entry_revision=ENTRY,source_manifest={n:pin(v) for n,v in source.items()},transfer_manifest=manifest,
        transfer_manifest_root=root,receiver=pin(receiver),changed_files=changed,entry_deltas=delta,
        function_identities=identities,unchanged_files=sorted(n for n in rows if rows[n]==source[n]),
        unchanged_policy_bundles={n:pin(item['source'].encode()) for n,item in json.loads(rows['FinalNativeGate_reviewed.json']).items()},
        no_final_charge_authority=True,execution_performed=False,print_axioms='N/A',
        caveat='AST/source identities are not OS/native semantics; fresh actual cleanup permission/control and complete pin approval remain open')
    with (release/'FinalNativeGate-release-identities.json').open('xb') as f:f.write(dump(report))
    with (release/'FinalNativeGate-data-activation.patch.txt').open('x') as f:f.write(''.join(diff))
    with (release/'FinalNativeGate-release-manifest.txt').open('x') as f:
        f.write('PROSPECTIVE ONLY; STOP for lead source/release review and explicit new allocation.\n')
        f.write('Exactly one future SSH candidate DATA action. No invocation authorized now.\n')
        f.write('Fixed host dombarker@100.108.41.90; fixed fresh-absent STAGE '+STAGE+'\n')
        f.write('Receiver sha256 '+pin(receiver)['sha256']+' size '+str(len(receiver))+'\n')
        f.write('Transfer root '+root+'; exact files in FinalNativeGate-release-identities.json.\n')
        f.write('Relative to maintained source-022: exactly two SETUP mains activate and four seal/plan files regenerate. Source-022 restores compatible disappeared outcomes after verified absence, including pidfd-signal; first v6 candidate and complete function diff retained in source022. Corrected prospective bytes supersede the first v6 candidate, not its historical byte identity. Historical v1-v5 artifacts remain byte-identical. Stage existence UNKNOWN; reject ANY entry.\n')
        f.write('FINAL mains disabled; no final charge authority. Source copies identify activated DATA overlay, never historical disabled identity.\n')
        f.write('Fixed target/harness/registry pins remain reads; absent files produce exact partial failure, never implicit upload.\n')
        f.write('0700 exclusive new leaf; retained partial failures; code sources remain stable while own packet children are created.\n')
        f.write('Outer transport120s and public combined output4MiB; >5MB derived JSON stays remote with size/hash.\n')
        f.write('Timeout/disconnection can leave remote work unresolved; no native cancellation guarantee from source/mocks.\n')
    return report

if __name__=='__main__':
    report=prepare()
    print(json.dumps(dict(files=len(report['transfer_manifest']),receiver=report['receiver'],execution_performed=False)))
