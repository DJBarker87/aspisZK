#!/usr/bin/env python3
"""Local controller. Remote ordinary-owner reads only; no remote stage/build."""
import ast, base64, hashlib, json, os, resource, subprocess, sys, time, uuid
from pathlib import Path
T=Path(__file__).resolve().parent
E=T.parents[1]/'evidence/port28rootexport-20261024'
SSH=['ssh','-o','BatchMode=yes','-o','ConnectTimeout=10','dombarker@100.108.41.90']
def sha(b): return hashlib.sha256(b).hexdigest()
def observe(label):
    body=(T/'Port28ROOTEXPORT_proc-all-v2.py').read_bytes(); start=time.monotonic()
    cmd=SSH+['sudo -n python3 -']; p=subprocess.run(cmd,input=body,capture_output=True,timeout=55)
    (E/f'Port28ROOTEXPORT_{label}.json').write_bytes(p.stdout)
    (E/f'Port28ROOTEXPORT_{label}.stderr.txt').write_bytes(p.stderr)
    r=dict(command=cmd,exit_status=p.returncode,wall_seconds=time.monotonic()-start,
           script_sha256=sha(body),output_sha256=sha(p.stdout),revision=subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip())
    (E/f'Port28ROOTEXPORT_{label}.receipt.json').write_text(json.dumps(r,indent=2)+'\n')
    assert p.returncode==0,p.stderr
    x=json.loads(p.stdout)
    print(label,x['allowed_to_enter'],flush=True)
    assert x['allowed_to_enter'], 'Metadata admission denied; retain result, no donor contents read'
    return x

def main():
    label=sys.argv[1]
    if label.startswith('observe-'): observe(label); return
    assert label=='copy'
    gate=json.loads((E/'Port28ROOTEXPORT_host-gate.json').read_text())
    assert gate['host_gate'].startswith('RELEASED')
    observe('copy-pre-v2')
    plan=json.loads((E/'Port28ROOTEXPORT_seed-plan.json').read_text())
    roots=list(dict.fromkeys(plan['ordered_original_lean_path']))
    graph=json.loads((E/'Port28ROOTEXPORT_source-import-plan.json').read_text())
    # Project modules only. No package-wide/sysroot content sweep. Missing header
    # and ConstantInfo dependencies remain explicit diagnostic gaps.
    modules=sorted(graph['modules'])
    request=dict(roots=roots,modules=modules,historical=plan['historical_direct_object_pins'],observer=(T/'Port28ROOTEXPORT_proc-all-v2.py').read_text())
    remote=(T/'Port28ROOTEXPORT_read.py').read_text()
    body=('REQUEST='+repr(request)+'\n'+remote).encode(); ast.parse(body)
    retained=Path('/private/tmp')/('port28rootexport-20261024-'+uuid.uuid4().hex)
    retained.mkdir(mode=0o700)
    (retained/'request.json').write_text(json.dumps(request,indent=2)+'\n')
    (retained/'remote-input.py').write_bytes(body)
    (E/'Port28ROOTEXPORT_retained.json').write_text(json.dumps(dict(path=str(retained),request_sha256=sha((retained/'request.json').read_bytes()),remote_input_sha256=sha(body)),indent=2)+'\n')
    cmd=SSH+['python3 -'];start=time.monotonic()
    rows=[];p=subprocess.Popen(cmd,stdin=subprocess.PIPE,stdout=subprocess.PIPE,stderr=(retained/'remote.stderr.txt').open('xb'))
    p.stdin.write(body);p.stdin.close()
    with (retained/'stream.jsonl').open('xb') as log:
        for line in p.stdout:
            x=json.loads(line)
            if x['kind']=='part':
                data=base64.b64decode(x.pop('base64'));assert sha(data)==x['sha256'] and len(data)==x['bytes']
                dest=retained/'objects'/str(x['root_index'])/x['relative_path']
                dest.parent.mkdir(parents=True,exist_ok=True)
                with dest.open('xb') as f: f.write(data)
                st=dest.stat();assert st.st_nlink==1
                x['retained_path']=str(dest);x['destination_inode']=st.st_ino
                x['copy_sha256']=sha(dest.read_bytes());assert x['copy_sha256']==x['sha256']
                rows.append({k:v for k,v in x.items() if k!='ancestors'})
            log.write((json.dumps(x,sort_keys=True)+'\n').encode());log.flush()
    code=p.wait();u=resource.getrusage(resource.RUSAGE_CHILDREN)
    summary=dict(command=cmd,exit_status=code,wall_seconds=time.monotonic()-start,child_peak_rss_bytes=u.ru_maxrss,swaps=u.ru_nswap,
        retained=str(retained),remote_input_sha256=sha(body),source_revision=subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip(),
        objects=rows,stream_sha256=sha((retained/'stream.jsonl').read_bytes()),print_axioms='N/A: untrusted data copy; no theorem',
        limitation='Sequential metadata and pre/copy/post hashes do not prove atomicity, no concurrent writer, historical part provenance, or future TOU identity')
    (E/'Port28ROOTEXPORT_copy.json').write_text(json.dumps(summary,indent=2)+'\n')
    assert code==0, f'Remote copy failed {code}; retain partial data'
    observe('copy-post')
    print(json.dumps(dict(parts=len(rows),bytes=sum(x['bytes'] for x in rows),retained=str(retained))))
if __name__=='__main__':main()
