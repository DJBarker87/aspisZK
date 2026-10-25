"""Versioned offline API. Pure evaluate() has no provenance or live authority."""
from pathlib import PurePosixPath
from ResourceAvailable_candidate import uint, add, GIB, LIMIT, membership, observe

def bind_scope(snapshot, expected):
    observe(snapshot)
    if set(expected) != {'high', 'cap', 'swap_max', 'tasks_max'}:
        raise ValueError('missing/unknown expected limits')
    for value in expected.values(): uint(value)
    if not (0 < expected['high'] <= expected['cap'] <= 8*GIB and
            expected['high'] <= 6*GIB and expected['swap_max'] == 0 and expected['tasks_max'] == 64):
        raise ValueError('invalid expected scope limits')
    identity = snapshot['self_observation']
    uint(identity['starttime'])
    unified = identity['unified_path']
    if not unified.startswith('/') or str(PurePosixPath(unified)) != unified or '..' in PurePosixPath(unified).parts:
        raise ValueError('noncanonical self cgroup path')
    path = identity['path']
    # Pure replay checks recorded procfs binding; public live entrypoint is disabled.
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
    a = observe(snapshot)
    association = next(d['covered_by'] for d in a['diagnostics'] if d['path'] == path)
    if association is None or association not in a['frontier']:
        raise ValueError('actual scope absent from finite frontier coverage')
    return dict(self_identity={k:v for k,v in identity.items() if k != 'reads'},
                expected_limits=expected, observed_limits=observed,
                finite_frontier_association=association, ancestor_limits=ancestors)


def evaluate(old, before, after, requested, *, phase, expected=None):
    out = dict(schema='ResourceAvailable20261024-v1', phase=phase, additional_bytes=requested, expected_limits=expected, adopted=False,
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
        if not isinstance(old, dict) or not old or old.get('error') or old.get('visibility_error'):
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
        a, b = observe(before), observe(after)
        old_frontier = [r['path'] for r in old['cgroups'] if r.get('charged_bytes', 0)]
        if old_frontier != a['frontier'] or uint(old['projected_reserved_bytes']) != add((a['bounded_reserved_bytes'], requested)):
            raise ValueError('legacy/frontier changed')
        projected = add((a['bounded_reserved_bytes'], requested))
        minimum = min(a['mem_available'], b['mem_available'])
        active = max(a['active_file_bytes'], b['active_file_bytes'])
        kernel = max(a['kernel_withheld_bytes'], b['kernel_withheld_bytes'])
        residual = max(a['root_residual_bytes'], b['root_residual_bytes'])
        deductions = add((active, kernel, residual))
        adjusted = uint(minimum - deductions)
        required = add((projected, 7*GIB))
        cap_ok = projected < LIMIT
        available_ok = minimum > add((requested, 2*GIB))
        legacy_gate_ok = old['allowed'] is True or old['reserve_check'] is False
        out.update(before_observation=a, after_observation=b,
            projected_reserved_bytes=projected, min_mem_available_bytes=minimum,
            max_active_file_bytes=active, max_kernel_withheld_bytes=kernel,
            max_root_residual_bytes=residual, adjusted_available_bytes=adjusted,
            required_bytes=required, margin_bytes=adjusted-required,
            cap_ok=cap_ok, available_ok=available_ok,
            legacy_nonreserve_gate_ok=legacy_gate_ok,
            allowed=cap_ok and available_ok and legacy_gate_ok and required < adjusted)
    except (KeyError, TypeError, ValueError, OverflowError, StopIteration, IndexError) as error:
        out['error'] = f'{type(error).__name__}: {error}'
    return out


def read_only_admission(*, phase, additional_bytes, expected=None):
    raise RuntimeError('ResourceAvailable offline-only; live boundary DISABLED')
