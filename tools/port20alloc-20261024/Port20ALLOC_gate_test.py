#!/usr/bin/env python3
import importlib.util, json, pathlib, tempfile
spec=importlib.util.spec_from_file_location('gate',pathlib.Path(__file__).with_name('Port20ALLOC_gate.py'))
gate=importlib.util.module_from_spec(spec); spec.loader.exec_module(gate)
with tempfile.TemporaryDirectory() as t:
    root=pathlib.Path(t)
    def node(name,pop=1,cap='max',ids=''):
        p=root/name; p.mkdir(parents=True,exist_ok=True)
        for k,v in {'cgroup.events':f'populated {pop}\n','cgroup.type':'domain',
                    'cgroup.procs':ids,'cgroup.subtree_control':'memory','memory.max':str(cap),
                    'memory.current':'999999999'}.items(): (p/k).write_text(v)
        return p
    node(''); node('system.slice'); node('system.slice/docker.service',cap=4*gate.G,ids='1\n')
    node('user.slice'); node('user.slice/parent',cap=7*gate.G)
    node('user.slice/parent/child',cap=2*gate.G,ids='2\n')
    node('retired',pop=0,cap=40*gate.G); node('service',ids='3\n')
    rows=gate.hierarchy(root)
    assert sum(r.get('reservation_bytes',0) for r in rows)==11*gate.G
    by={r['path']:r for r in rows}
    assert by['user.slice/parent/child']['effective_cover']=='user.slice/parent'
    assert by['service']['effective_cover'] is None
    assert 'reservation_bytes' not in by['retired']
    (root/'system.slice/docker.service/memory.max').unlink()
    try: gate.hierarchy(root)
    except AssertionError: pass
    else: raise AssertionError('missing cap did not deny')
    node('system.slice/docker.service',cap=5*gate.G)
    assert gate.topology(rows)!=gate.topology(gate.hierarchy(root))
print(json.dumps(dict(nested_dedup=True,inactive_pagecache_not_reserved=True,
    empty_parent_live_child=True,system_docker_services_visible=True,
    missing_controller_file_denies=True,changed_limits_detected=True)))
