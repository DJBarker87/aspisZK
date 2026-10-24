#!/usr/bin/env python3
"""One remote stdin-only diagnostic; writes evidence only in this worktree.

No remote files, systemd scopes, probes, caches, or consumer jobs are created.
"""
import hashlib
import json
import pathlib
import resource
import subprocess
import time

HERE=pathlib.Path(__file__).resolve().parent
OUT=HERE.parent.parent/'evidence/resource-slab-20261024'
HOST='dombarker@100.108.41.90'


def digest(path):
    data=path.read_bytes()
    return dict(sha256=hashlib.sha256(data).hexdigest(),size=len(data))


def save(name, data):
    raw=(json.dumps(data,indent=2)+'\n').encode()
    if len(raw)>5_000_000:
        # Oversized derived output is deliberately not committed.
        raw=(json.dumps(dict(omitted=True,sha256=hashlib.sha256(raw).hexdigest(),size=len(raw)))+'\n').encode()
    (OUT/name).write_bytes(raw)


def main():
    files=['reservation.py','reservation_base.py','resource_slab_candidate.py']
    hashes={f:digest(HERE/f) for f in files}
    sources={f:(HERE/f).read_text() for f in files}
    # Only __file__ reads / run_path of the immutable legacy helper are
    # virtualized. All sysfs/proc/service/process/Docker reads are unchanged.
    payload='''import hashlib, json, pathlib, runpy\nSOURCES=REPLACE_SOURCES\nHASHES=REPLACE_HASHES\noriginal_read=pathlib.Path.read_bytes\ndef virtual_read(path):\n    if str(path).startswith('/resource-slab-virtual/'):\n        return SOURCES[path.name].encode()\n    return original_read(path)\npathlib.Path.read_bytes=virtual_read\ndef virtual_run(path):\n    name=pathlib.Path(path).name\n    ns={'__file__':'/resource-slab-virtual/'+name,'__name__':'resource_slab_virtual'}\n    exec(compile(SOURCES[name],ns['__file__'],'exec'),ns)\n    return ns\nrunpy.run_path=virtual_run\nlegacy=virtual_run('reservation.py')\ncandidate=virtual_run('resource_slab_candidate.py')\nprint(json.dumps(candidate['live'](legacy['admission'],HASHES)))\n'''.replace('REPLACE_SOURCES',repr(sources)).replace('REPLACE_HASHES',repr(hashes))
    command=['ssh','-o','BatchMode=yes','-o','ConnectTimeout=10',HOST,'python3 -B -']
    start=time.monotonic()
    result=subprocess.run(command,input=payload,text=True,capture_output=True,timeout=120)
    receipt=dict(command=command, stdin_sha256=hashlib.sha256(payload.encode()).hexdigest(),
                 source_version=subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip(),
                 source_hashes=hashes, exit=result.returncode, wall_seconds=time.monotonic()-start,
                 local_peak_rss_bytes=resource.getrusage(resource.RUSAGE_CHILDREN).ru_maxrss,
                 local_swaps=resource.getrusage(resource.RUSAGE_CHILDREN).ru_nswap,
                 host_scope='N/A: read-only diagnostics, no scope allocation authorized',
                 print_axioms='N/A; formal budget ZERO',stderr=result.stderr)
    save('live-command.json',receipt)
    (OUT/'live-stdin.py.txt').write_text(payload)
    if result.returncode:
        raise SystemExit(result.returncode)
    report=json.loads(result.stdout)
    snapshots=report.pop('snapshots')
    decisions=report.pop('decisions')
    original=report.pop('original_legacy')
    save('live-summary.json',report)
    save('legacy-snapshot.json',original)
    for phase,snapshot in snapshots.items():
        if snapshot:
            raw=snapshot.pop('raw_inputs')
            # Shard raw interfaces by group: retain every exact source value.
            paths={}
            for path,value in raw.items(): paths.setdefault(str(pathlib.PurePosixPath(path).parent),{})[path]=value
            for i,(group,inputs) in enumerate(sorted(paths.items())):
                save(f'inputs-{phase}-{i:03d}.json',dict(group=group,inputs=inputs))
        save('snapshot-'+phase+'.json',snapshot)
    for size,decision in decisions.items():
        save('decision-'+size+'GiB.json',decision)
    print(json.dumps(dict(exit=result.returncode,collection_error=report['collection_error'],
                        decisions={k:dict(allowed=v['allowed'],error=v.get('error'),
                                          estimate=v.get('estimated_total_bytes')) for k,v in decisions.items()})))

if __name__=='__main__': main()
