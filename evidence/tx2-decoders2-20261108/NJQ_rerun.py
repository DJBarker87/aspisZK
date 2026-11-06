"""Exact historical native inputs; only owned path relocation and isolation added."""
from NJQ_transport import *
import hashlib,lzma,base64,shlex,sys
sha=lambda b:hashlib.sha256(b).hexdigest()
def historical(old):
    p=E.parent/('slice-d-entry5-20261107' if old.startswith('NIJ_') else 'slice-d-entry4-20261106')
    cfg=(p/(old+'.json')).read_bytes();x=json.loads(cfg)
    idx=json.loads((p/(old[:3]+'_INPUTS.json')).read_text())
    files={}
    for name,h in idx['attempts'][old].items():
        z=p/idx['objects'][h]['path'];raw=lzma.decompress(z.read_bytes());assert sha(raw)==h
        files[name]=raw.decode()
    for name,h in json.loads((p/old/'receipt.json').read_text())['source_hashes'].items():assert sha(files[name].encode())==h
    # Always restore owned parents omitted by the historical incremental payload.
    # Every added byte is checked against the original strict source pin.
    pins=json.loads(files['NIJ_SOURCE_PINS.json'])
    for parent in ['crates/aspis-statement/src/pool_v1/format.rs','crates/aspis-statement/src/pool_v1/verifier_registry.rs','crates/aspis-statement/src/pool_v1/pair_forest_accounts.rs']:
        key='NIJ_src/'+parent
        if key not in files:
            raw=subprocess.check_output(['git','show','4bb3b3f51e16b4525f1d10336e2b0bcbbd775387:'+parent])
            assert sha(raw)==pins[parent]
            files[key]=raw.decode()
    return x,cfg,files
def run(a,old,prepared=None):
    assert a.startswith('NJQ_K') and 1<=int(a[-3:])<=60
    assert not (E/a).exists()
    x,original,files=historical(old) if prepared is None else prepared
    oldB=str(Path(x['native_command'][x['native_command'].index('--manifest-path')+1]).parents[3])
    # Explicit known workspace root, not guessed from crate nesting.
    oldB='/home/dombarker/project-offloads/'+('codex-cx-slice-d-entry5-20261107' if old.startswith('NIJ_') else 'codex-cx-slice-d-entry4-20261106')
    origcommand=list(x['native_command']);oldtarget=origcommand[origcommand.index('--target-dir')+1]
    x['native_command']=[s.replace(oldB+'/',B+'/') for s in origcommand]
    x['native_command'][x['native_command'].index('--target-dir')+1]=B+'/NJQ_target'
    for k in ['metadata_manifest']:
        if k in x:x[k]=x[k].replace(oldB+'/',B+'/')
    # Original gate and erasure implementation remain byte-identical.
    x.update(attempt=a,original_attempt=old,original_config_file='NJQ_originals/'+old+'.json',original_config_sha256=sha(original),old_target=oldtarget,historical_gate_command=[*x['command'][:-1],a+'.json'],command=['python3','NJQ_isolation.py',a+'.json'],source_revision=subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip(),source_tree_dirty=True)
    x['env'].update(TMPDIR=B+'/NJQ_tmp',CARGO_TARGET_DIR=B+'/NJQ_target',CARGO_NET_OFFLINE='true')
    files[x['original_config_file']]=original.decode()
    files['NJQ_isolation.py']=(E/'NJQ_isolation.py').read_text()
    x['sources']+=['NJQ_isolation.py',x['original_config_file']]
    files[a+'.json']=json.dumps(x,indent=1)+'\n'
    # Pin all inputs once by hash locally. No historical input is omitted.
    idx=json.loads((E/'NJQ_INPUTS.json').read_text()) if (E/'NJQ_INPUTS.json').exists() else dict(objects={},attempts={})
    inputs={}
    for n,t in files.items():
        raw=t.encode();h=sha(raw);q=E/'NJQ_INPUTS'/(h+'.xz');q.parent.mkdir(exist_ok=True)
        if not q.exists():q.write_bytes(lzma.compress(raw))
        idx['objects'][h]=dict(path=str(q.relative_to(E)),bytes=len(raw),archive_sha256=sha(q.read_bytes()));inputs[n]=h
    idx['attempts'][a]=inputs;(E/'NJQ_INPUTS.json').write_text(json.dumps(idx,indent=1)+'\n')
    (E/(a+'.json')).write_text(files[a+'.json'])
    admission(a)
    payload=base64.b64encode(lzma.compress(json.dumps(files).encode())).decode()
    r=ssh('python3',f'''from pathlib import Path
import json,lzma,base64
b=Path({B!r});files=json.loads(lzma.decompress(base64.b64decode({payload!r})))
for n,t in files.items():
 p=b/n;assert p.resolve().is_relative_to(b.resolve());p.parent.mkdir(parents=True,exist_ok=True);p.write_text(t)
''');assert r.returncode==0,r.stderr
    r=ssh('cd '+shlex.quote(B)+' && systemd-run --user --scope -p MemoryHigh=6G -p MemoryMax=8G -p MemorySwapMax=0 -p TasksMax=64 python3 S2W_run_host.py '+a+'.json',submitted=True)
    (E/(a+'-launcher.log')).write_text(r.stdout+r.stderr)
    r=ssh('python3',f'''from pathlib import Path
import json,hashlib
b=Path({B!r});a={a!r}
paths=[p for p in (b/a).rglob('*') if p.is_file() and 'sources' not in p.relative_to(b/a).parts]
paths += [p for pat in ['-graph*','-source*','-lock*','-erasure*','-isolation.json'] for p in b.glob(a+pat)]
rc=json.loads((b/a/'receipt.json').read_text())
for n,h in rc['source_hashes'].items():assert hashlib.sha256((b/a/'sources'/n).read_bytes()).hexdigest()==h
print(json.dumps({{str(p.relative_to(b)):p.read_text() for p in paths}}))
''');assert r.returncode==0,r.stderr
    out=json.loads(r.stdout)
    for n,t in out.items():
        p=E/n;p.parent.mkdir(parents=True,exist_ok=True)
        if n.endswith('.log'):
            p.with_name(p.name+'.xz').write_bytes(lzma.compress(t.encode()));p.with_name(p.name+'.sha256').write_text(sha(t.encode())+'\n')
        else:p.write_text(t)
    rc=json.loads(out[a+'/receipt.json'])
    with (E/'NJQ_ATTEMPTS.jsonl').open('a') as f:f.write(json.dumps(rc)+'\n')
    expected=json.loads((E.parent/('slice-d-entry5-20261107' if old.startswith('NIJ_') else 'slice-d-entry4-20261106')/old/'receipt.json').read_text())['exit_status'] if prepared is None else None
    summary=dict(attempt=a,original=old,exit=rc['exit_status'],expected=expected,wall=rc['wall_seconds'],rss=rc['peak_rss_kib'],same_verdict=expected==rc['exit_status'] if expected is not None else None)
    with (E/'NJQ_RERUN_RESULTS.jsonl').open('a') as f:f.write(json.dumps(summary)+'\n')
    print(json.dumps(summary),flush=True)
    if expected is not None and expected!=rc['exit_status']:raise RuntimeError('NIS-F1: historical verdict changed; preserve finding, do not reconcile')
    return rc
if __name__=='__main__':run(*sys.argv[1:])
