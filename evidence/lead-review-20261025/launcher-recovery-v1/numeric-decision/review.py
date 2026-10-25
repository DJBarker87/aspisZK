"""Offline arithmetic evidence only; never scans, admits, allocates, or launches."""
import hashlib
import json
from pathlib import Path
import resource
import subprocess
import time

start = time.monotonic()
G = 2**30
OUT = Path(__file__).resolve().parent
ROOT = OUT.parents[3]
CAPTURE = Path('/private/tmp/Port36LINUX-publication-action-20261025-v1/stdout.log')
raw = CAPTURE.read_bytes()
assert len(raw) == 15473168
assert hashlib.sha256(raw).hexdigest() == '279909c5bbd0a7c1f281d6bf217de8b59a85ed6c8ec0f9f14ee24d568977bd94'
a = json.loads(raw)['admission']
d = a['decision']
receipt_path = OUT.parent/'pids-accounting-v4/actual-publication-result.json'
receipt = json.loads(receipt_path.read_text())
for key in ('allowed', 'margin_bytes', 'adjusted_available_bytes', 'required_bytes'):
    assert d[key] == receipt['decision'][key]
assert not d['membership_differences']
assert receipt['decision']['snapshots_completed'] == {'before': True, 'after': True}
minimum = min(s['meminfo']['MemAvailable'] for s in a['snapshots'].values())
active = max(s['meminfo']['Active(file)'] for s in a['snapshots'].values())
kernel = max(s['meminfo']['KReclaimable']-s['meminfo']['SReclaimable']//2 for s in a['snapshots'].values())
residual = max(d[k+'_observation']['root_residual_bytes'] for k in ('before','after'))
frontier = d['before_observation']['bounded_reserved_bytes']
assert frontier == d['after_observation']['bounded_reserved_bytes'] == 26172456960
adjusted = minimum-active-kernel-residual
required = frontier+8*G+7*G
assert (adjusted, required, adjusted-required) == (36503900160,42278584320,-5774684160)
# Scalar policy tests, not synthetic hierarchy validity or admission authorization.
def numeric(available, existing=frontier, requested=8*G, deductions=active+kernel+residual):
    return existing+requested < 55*G and available > requested+2*G and existing+requested+7*G < available-deductions
cases = []
def case(name, actual, expected):
    assert actual == expected, name
    cases.append(dict(name=name, result=actual, expected=expected))
case('captured strict denial', numeric(minimum), False)
case('exact adjusted equality still denies', numeric(minimum+5774684160), False)
case('one byte beyond adjusted equality passes numeric gates only', numeric(minimum+5774684161), True)
case('six GiB less existing reservation passes numeric gates only', numeric(minimum, existing=frontier-6*G), True)
case('five GiB less existing reservation still denies', numeric(minimum, existing=frontier-5*G), False)
case('55 GiB reservation equality denies despite ample availability', numeric(100*G, existing=47*G), False)
case('two GiB availability guard equality denies', numeric(10*G, existing=0, deductions=0), False)
case('historical Port17 reservation-only test passes', frontier+8*G < 55*G, True)
summary = {}
for name, s in a['snapshots'].items():
    rows=s['rows']; f=set(d[name+'_observation']['frontier'])
    top=sum(r['current'] for r in rows if r['enabled'] and r['owner']==rows[0]['path'])
    capped=sum(r['current'] for r in rows if r['path'] in f)
    summary[name]=dict(rows=len(rows), mem_total_bytes=s['meminfo']['MemTotal'], frontier_current_bytes=capped,
                       accounted_current_outside_frontier_bytes=top-capped)
pins = {}
for rev, path in [('f7b90c82300c8a2409625fefb5dc529db6547f9c','tools/resource-stability-20261025/ResourceStability_evaluator.py'),
                  ('49f36dfb1b','tools/port17release-20261024/Port17RELEASE_admission.py')]:
    data=subprocess.check_output(['git','show',rev+':'+path],cwd=ROOT)
    pins[rev+':'+path]=dict(bytes=len(data),sha256=hashlib.sha256(data).hexdigest())
p='tools/port36transport-20261025/linux367/Port36LINUX_pid_candidate.py'
data=(ROOT/p).read_bytes()
pins[p]=dict(bytes=len(data),sha256=hashlib.sha256(data).hexdigest())
r=resource.getrusage(resource.RUSAGE_SELF); children=resource.getrusage(resource.RUSAGE_CHILDREN)
result=dict(command='python3 evidence/port36transport-20261025/linux367/numeric-denial-review/review.py',
 source_revision=subprocess.check_output(['git','rev-parse','HEAD'],cwd=ROOT,text=True).strip(), pins=pins,
 capture=dict(path=str(CAPTURE),bytes=len(raw),sha256=hashlib.sha256(raw).hexdigest()),
 arithmetic=dict(minimum_bytes=minimum,active_bytes=active,kernel_bytes=kernel,residual_bytes=residual,
 frontier_bytes=frontier,requested_bytes=8*G,reserve_bytes=7*G,adjusted_bytes=adjusted,required_bytes=required,
 deficit_bytes=required-adjusted,deficit_GiB=(required-adjusted)/G),snapshots=summary,cases=cases,
 exit_status=0,wall_seconds=time.monotonic()-start,peak_self_RSS_bytes=r.ru_maxrss,
 peak_serial_child_RSS_bytes=children.ru_maxrss,self_swap_counter=r.ru_nswap,child_swap_counter=children.ru_nswap,
 metric_units='Darwin ru_maxrss bytes; ru_nswap counters, not measured swap bytes',
 print_axioms='N/A; no Lean/proof invocation',policy_change=False,security_targets='both NOT ESTABLISHED')
(OUT/'result.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps({k:result[k] for k in ('exit_status','wall_seconds','peak_self_RSS_bytes','peak_serial_child_RSS_bytes','self_swap_counter','child_swap_counter')}))
