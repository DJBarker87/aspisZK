#!/usr/bin/env python3
"""ResourceStat unadopted phase adapter. Derived from immutable 25b0b9df48. Observations are evidence, never launch authority.

The public live adapter accepts no caller-supplied cgroup path or PID. Pure
snapshot evaluation is replayable and is not a claim of live provenance.
"""
import hashlib
import os
from pathlib import Path, PurePosixPath
import runpy

base = runpy.run_path(str(Path(__file__).with_name('ResourceStat_candidate.py')))
for name in ('uint', 'add', 'GIB', 'LIMIT', 'membership', 'accounting'):
    globals()[name] = base[name]
API_VERSION = 'ResourceStat-GO-phase-v1'


def self_observation():
    """Derive identity and scope from actual procfs, with ordered raw receipts."""
    reads = []
    def read(path):
        try:
            value = Path(path).read_text()
        except OSError as exc:
            reads.append(dict(path=path, errno=exc.errno, error=str(exc)))
            raise
        reads.append(dict(path=path, content=value, errno=0,
                          sha256=hashlib.sha256(value.encode()).hexdigest()))
        return value
    def identity(raw):
        prefix, tail = raw.rsplit(')', 1)
        return dict(pid=base['parse_number'](prefix.split(' ', 1)[0]),
                    starttime=base['parse_number'](tail.split()[19]))
    try:
        first = identity(read('/proc/self/stat'))
        status = dict(line.split(':', 1) for line in read('/proc/self/status').splitlines())
        groups = read('/proc/self/cgroup')
        second = identity(read('/proc/self/stat'))
        pid = os.getpid()
        if first != second or first['pid'] != pid or any(
                base['parse_number'](status[k].strip()) != pid for k in ('Pid', 'Tgid')):
            raise ValueError('self process identity race')
        paths = [line[3:] for line in groups.splitlines() if line.startswith('0::')]
        if len(paths) != 1:
            raise ValueError('missing/ambiguous unified self membership')
        path = paths[0]
        if not path.startswith('/') or str(PurePosixPath(path)) != path or '..' in PurePosixPath(path).parts:
            raise ValueError('noncanonical self cgroup path')
        return dict(**first, unified_path=path, path='/sys/fs/cgroup'+('' if path == '/' else path), reads=reads)
    except (OSError, ValueError, KeyError, IndexError) as exc:
        exc.read_attempts = reads
        exc.partial_raw_inputs = {r['path']:r['content'] for r in reads if 'content' in r}
        raise


def scan_bound():
    """Both self observations bracket the full unchanged hierarchy scan."""
    first = self_observation()
    try:
        snapshot = base['scan']()
        second = self_observation()
        if {k:v for k,v in first.items() if k != 'reads'} != {k:v for k,v in second.items() if k != 'reads'}:
            raise ValueError('self membership/identity race across scan')
        snapshot['self_observation'] = first
        snapshot['self_read_attempts'] = first['reads']+second['reads']
        return snapshot
    except (OSError, ValueError, KeyError, IndexError) as exc:
        attempts = first['reads'] + (snapshot.get('read_attempts', []) if 'snapshot' in locals() else [])
        attempts += second['reads'] if 'second' in locals() else getattr(exc, 'read_attempts', [])
        exc.read_attempts = attempts
        exc.partial_raw_inputs = {r['path']:r['content'] for r in exc.read_attempts if 'content' in r}
        raise


def bind_scope(snapshot, expected):
    if set(expected) != {'high', 'cap', 'swap_max', 'tasks_max'}:
        raise ValueError('missing/unknown expected limits')
    for value in expected.values(): uint(value)
    if not (0 < expected['high'] <= expected['cap'] <= 8*GIB and
            expected['high'] <= 6*GIB and expected['swap_max'] == 0 and expected['tasks_max'] == 64):
        raise ValueError('invalid expected scope limits')
    identity = snapshot['self_observation']
    path = identity['path']
    # Pure replay checks binding to recorded procfs; live entrypoint supplies it.
    expected_path = '/sys/fs/cgroup'+('' if identity['unified_path']=='/' else identity['unified_path'])
    if path != expected_path:
        raise ValueError('fake self cgroup path')
    by = {r['path']:r for r in snapshot['rows']}
    row = by[path]
    if row['root'] or not path.endswith('.scope') or row['type'] != 'domain' or not row['enabled'] or not row['populated'] or not row['pids_enabled']:
        raise ValueError('self is not a populated memory-enabled domain scope')
    observed = {key:row[key] for key in expected}
    if observed != expected:
        raise ValueError('actual scope controls differ from declared expectations')
    if row['swap_current'] != 0:
        raise ValueError('scope already uses swap')
    pid = uint(identity['pid'])
    if pid == 0 or pid not in row['procs'] or not any(
            i == dict(tid=pid, tgid=pid, starttime=identity['starttime']) for i in row['identities']):
        raise ValueError('own PID/starttime missing from actual scope membership')
    ancestors = []
    parent = row['parent']
    while parent is not None:
        ancestor = by[parent]
        if ancestor['enabled']:
            # memory.high also constrains actual operation; no weaker ancestor
            # than the declared scope limits is silently accepted.
            for key in ('cap', 'high'):
                limit = ancestor[key]
                if limit is not None and limit < expected[key]:
                    raise ValueError('effective ancestor '+key+' below expected limit')
            ancestors.append(dict(path=parent, cap=ancestor['cap'], high=ancestor['high']))
        if ancestor['pids_enabled'] and ancestor['tasks_max'] is not None and ancestor['tasks_max'] < expected['tasks_max']:
            raise ValueError('effective ancestor tasks cap below expected limit')
        parent = ancestor['parent']
    a = accounting(snapshot)
    association = next(d['covered_by'] for d in a['exclusive'] if d['path'] == path)
    if association is None or association not in a['frontier']:
        raise ValueError('actual scope absent from finite frontier coverage')
    return dict(self_identity={k:v for k,v in identity.items() if k != 'reads'},
                expected_limits=expected, observed_limits=observed,
                finite_frontier_association=association, ancestor_limits=ancestors)


def evaluate(old, before, after, requested, *, phase, expected=None):
    out = dict(schema=API_VERSION, phase=phase, additional_bytes=requested, expected_limits=expected, adopted=False,
               allowed=False, legacy=old, requested_bytes=requested,
               os_control_bytes=7*GIB, safe_limit_bytes=LIMIT,
               required_consumer_scope=dict(MemoryHigh='6G', MemoryMax='8G',
                    MemorySwapMax=0, TasksMax=64, stricter_existing='5G/7G unchanged'),
               print_axioms='N/A; formal budget ZERO')
    try:
        uint(requested)
        if phase not in ('prospective', 'inside-scope'):
            raise ValueError('unknown phase')
        if phase == 'prospective' and (requested == 0 or expected is not None):
            raise ValueError('prospective requires positive additional reservation and no scope declaration')
        if phase == 'inside-scope':
            if requested != 0:
                raise ValueError('inside-scope GO requires zero additional bytes')
            first = bind_scope(before, expected)
            second = bind_scope(after, expected)
            if first != second:
                raise ValueError('self scope identity/control race')
            out['scope_binding'] = first
        if not old or old.get('error') or old.get('visibility_error'):
            raise ValueError('legacy visibility error/missing')
        for field in ('process_visibility', 'service_visibility', 'docker_visibility',
                      'cgroups', 'projected_reserved_bytes', 'allowed', 'reserve_check'):
            if field not in old:
                raise ValueError('missing legacy visibility: '+field)
        if (not isinstance(old['process_visibility'], str) or not old['process_visibility'].strip()
                or not isinstance(old['service_visibility'], str)
                or not isinstance(old['docker_visibility'], list)
                or not isinstance(old['cgroups'], list)
                or type(old['allowed']) is not bool or type(old['reserve_check']) is not bool):
            raise ValueError('invalid legacy visibility/decision types')
        if before is None or after is None:
            raise ValueError('missing hierarchy snapshot')
        if membership(before) != membership(after):
            raise ValueError('hierarchy/membership/control race')
        a, b = accounting(before), accounting(after)
        old_frontier = [r['path'] for r in old['cgroups'] if r.get('charged_bytes', 0)]
        if old_frontier != a['frontier'] or uint(old['projected_reserved_bytes']) != add((a['bounded_reserved_bytes'], requested)):
            raise ValueError('legacy/frontier changed')
        # Matched hierarchy, conservative per-exclusive-cell envelope. A racing
        # cell fallback disables both credits across the pair.
        envelope = []
        for x, y in zip(a['exclusive'], b['exclusive']):
            if x['covered_by'] is None:
                fallback = x['fallback'] or y['fallback']
                usage = max(x['conservative_charge'], y['conservative_charge'])
                inactive = 0 if fallback else min(x['inactive_file_credit'], y['inactive_file_credit'])
                slab = 0 if fallback else min(x['half_slab_credit'], y['half_slab_credit'])
                envelope.append(dict(path=x['path'], fallback=fallback, usage=usage, inactive_credit=inactive,
                                     half_slab_credit=slab, reserve=usage-inactive-slab))
        projected = add((a['bounded_reserved_bytes'], requested))
        estimate = add((projected, max(a['root_residual_bytes'], b['root_residual_bytes']),
                        add(r['reserve'] for r in envelope), 7*GIB))
        cap_ok = projected < LIMIT and uint(old['projected_reserved_bytes']) < LIMIT
        available_ok = min(a['mem_available'], b['mem_available']) > add((requested, 2*GIB))
        # The old allowed flag may be false ONLY because reserve_check failed.
        legacy_gate_ok = old['allowed'] is True or old['reserve_check'] is False
        out.update(before_accounting=a, after_accounting=b, envelope=envelope,
                   projected_reserved_bytes=projected, estimated_total_bytes=estimate,
                   cap_ok=cap_ok, available_ok=available_ok,
                   legacy_nonreserve_gate_ok=legacy_gate_ok,
                   coverage_added=[r['path'] for r in a['exclusive'] if r['covered_by'] is None and not r['populated']],
                   root_coverage_added=True,
                   allowed=cap_ok and available_ok and legacy_gate_ok and estimate < min(a['mem_total'], b['mem_total']))
    except (KeyError, TypeError, ValueError, OverflowError, StopIteration) as error:
        out['error'] = f'{type(error).__name__}: {error}'
    return out



def legacy_request(old, requested):
    """Algebraic request variant of one unchanged legacy measurement."""
    legacy = dict(old or {})
    if old and all(k in old for k in ('bounded_reserved_bytes', 'meminfo', 'uncapped_resident_reserve_bytes')):
        legacy['requested_bytes'] = requested
        legacy['projected_reserved_bytes'] = old['bounded_reserved_bytes']+requested
        legacy['reserve_check'] = (legacy['projected_reserved_bytes']+old['uncapped_resident_reserve_bytes']+7*GIB < old['meminfo']['MemTotal'] and old['meminfo']['MemAvailable'] > requested+2*GIB)
        legacy['allowed'] = (not old.get('error') and not old.get('visibility_error') and legacy['projected_reserved_bytes'] < LIMIT and legacy['reserve_check'])
    return legacy


def live(legacy_admission, source_hashes):
    """READONLY diagnostic. No supplied path, no reservation or consumer."""
    import datetime
    import resource
    import subprocess
    import time
    start = time.monotonic()
    old = None
    failures = {}
    snapshots = {}
    try:
        old = legacy_admission(requested=4*GIB)
    except (OSError, ValueError, subprocess.SubprocessError) as exc:
        failures['legacy'] = dict(error=str(exc))
    for phase in ('before', 'after'):
        try:
            snapshots[phase] = scan_bound()
        except (OSError, ValueError, KeyError, IndexError) as exc:
            snapshots[phase] = None
            failures[phase] = dict(error=str(exc), errno=getattr(exc, 'errno', None),
                raw_inputs=getattr(exc, 'partial_raw_inputs', None),
                read_attempts=getattr(exc, 'read_attempts', None))
    before, after = snapshots['before'], snapshots['after']
    decisions = {str(size):evaluate(legacy_request(old,size*GIB),before,after,size*GIB,
                                  phase='prospective') for size in (1,2,3,4,6,7,8)}
    # Diagnostic of actual collector identity, never a substitute scope. The
    # outside-scope observation must deny even if a hypothetical request fits.
    go = evaluate(legacy_request(old,0),before,after,0,phase='inside-scope',
                  expected=dict(high=6*GIB,cap=8*GIB,swap_max=0,tasks_max=64))
    usage = resource.getrusage(resource.RUSAGE_SELF)
    return dict(utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),
        source_hashes=source_hashes, api_version=API_VERSION, uname=os.uname().release,
        mode='READONLY PROPOSAL; no allocation, lock, consumer or adoption',
        snapshots=snapshots, original_legacy=old, decisions=decisions,
        actual_collector_go=go,
        collection_error='; '.join(k+': '+v['error'] for k,v in failures.items()) or None,
        failures=failures, wall_seconds=time.monotonic()-start,
        peak_rss_kib=usage.ru_maxrss, swaps=usage.ru_nswap, exit=0,
        print_axioms='N/A; formal budget ZERO')


def read_only_admission(*, phase, additional_bytes, expected=None):
    """Live adapter for later independent review; accepts no scope path or PID.

    Call only inside the caller's independently authorized existing scope for
    GO. Returns measured evidence and a proposal, never creates a reservation.
    The injectable evaluate() below this boundary is strictly offline replay.
    """
    import resource
    import time
    start = time.monotonic()
    old = before = after = None
    failures = {}
    try:
        legacy = runpy.run_path(str(Path(__file__).parent/'baseline'/'reservation.py'))
        old = legacy['admission'](requested=additional_bytes)
    except (OSError, ValueError, KeyError) as exc:
        failures['legacy'] = dict(error=str(exc))
    for label in ('before', 'after'):
        try:
            snapshot = scan_bound()
            if label == 'before': before = snapshot
            else: after = snapshot
        except (OSError, ValueError, KeyError, IndexError) as exc:
            failures[label] = dict(error=str(exc), errno=getattr(exc,'errno',None),
                read_attempts=getattr(exc,'read_attempts',[]))
    result = evaluate(old,before,after,additional_bytes,phase=phase,expected=expected)
    if failures:
        result.update(allowed=False, collection_failures=failures)
    usage = resource.getrusage(resource.RUSAGE_SELF)
    return dict(api_version=API_VERSION, decision=result,
        snapshots=dict(before=before,after=after),original_legacy=old,
        wall_seconds=time.monotonic()-start,peak_rss_kib=usage.ru_maxrss,
        swaps=usage.ru_nswap, print_axioms='N/A; formal budget ZERO')
