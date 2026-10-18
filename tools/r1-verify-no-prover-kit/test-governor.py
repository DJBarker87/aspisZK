#!/usr/bin/env python3
"""Pure process-classifier fixtures; no /proc mutation, compiler or native gate."""
import importlib.util
from pathlib import Path
s=importlib.util.spec_from_file_location('g',Path(__file__).with_name('governor.py'));g=importlib.util.module_from_spec(s);s.loader.exec_module(g)
own='0::/user.slice/user-1000.slice/user@1000.service/app.slice/r1-b-no-prover-test-20261018.scope';foreign='0::/user.slice/user-1000.slice/user@1000.service/app.slice/lead-build.scope'
records={1:{'ppid':0,'exe':'systemd','cgroup':'0::/'},100:{'ppid':1,'exe':'python3','cgroup':own},101:{'ppid':100,'exe':'cargo','cgroup':own},102:{'ppid':101,'exe':'rustc','cgroup':own},201:{'ppid':1,'exe':'aspis_pool_driver','cgroup':own},202:{'ppid':1,'exe':'aspis_pool_driver','cgroup':foreign},203:{'ppid':1,'exe':'lake','cgroup':foreign},204:{'ppid':1,'exe':'charon-r18-driver','cgroup':foreign},205:{'ppid':1,'exe':'aeneas-release','cgroup':foreign},206:{'ppid':1,'exe':'r1-pool-replay','cgroup':foreign},207:{'ppid':1,'exe':'lean','cgroup':'0::/user.slice/user-1000.slice/user@1000.service/app.slice'}}
assert [p['pid'] for p in g.classify(records,100,own)]==[202,203,204,205,206,207]
assert [p['pid'] for p in g.classify(records,100,None)]==[201,202,203,204,205,206,207]
assert [p['pid'] for p in g.classify(records,100,'0::/user.slice')] == [201,202,203,204,205,206,207]
print('PASS: own descendants and exact dedicated-scope reparented child exempt; foreign same-user scopes, broad-user prefix, lake, actual replay/tool executable names retained. No Rust/native job.')
