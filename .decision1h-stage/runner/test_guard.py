#!/usr/bin/env python3
"""Pure synthetic process/cgroup fixture; starts no child or compiler."""
import json
import host_gate as gate
scope='0::/user.slice/user-1000.slice/user@1000.service/app.slice/our-dedicated.scope'
foreign='0::/user.slice/user-1000.slice/user@1000.service/app.slice/lead.scope'
fixture={
 100:{'pid':100,'ppid':1,'comm':'cargo-build-sbf','argv':'own build'},
 101:{'pid':101,'ppid':100,'comm':'rustc','argv':'own --version'},
 102:{'pid':102,'ppid':1,'comm':'rustc','argv':'own reparented descendant'},
 999:{'pid':999,'ppid':1,'comm':'rustc','argv':'foreign same-user different scope'},
 998:{'pid':998,'ppid':1,'comm':'lean','argv':'foreign Lean different scope'},
}
gate.processes=lambda:fixture
gate.process_cgroup=lambda pid:scope if pid in [100,101,102] else foreign
found=gate.activity(own_job=100,own_cgroup=scope)
assert {p['pid'] for p in found}=={998,999}
# An explicitly foreign scope is never exempted by the common user.slice.
assert all(p['pid'] not in [100,101,102] for p in found)
print(json.dumps({'status':'PASS','synthetic_fixture_only':True,'compiler_or_child_started':False,'own_scope_excluded':[100,101,102],'foreign_scope_detected':sorted(p['pid'] for p in found),'scope_rule':'exact dedicated cgroup equality, not shared user prefix'}))
