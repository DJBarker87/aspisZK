"""ResourceStability v1 OFFLINE counterfactual policy, never admission authority.

Numerical evaluate body copied from pinned ResourceAvailable GO. Only explicit
self, structural comparison, unit binding and diagnostic additions differ.
"""
from pathlib import PurePosixPath
from ResourceStability_sources import c, go

uint, add, GIB, LIMIT, observe = c.uint, c.add, c.GIB, c.LIMIT, c.observe
bind_scope = go.bind_scope
API_VERSION = 'ResourceStability20261025-v1'
STRUCTURAL_FIELDS = (
    'path', 'parent', 'root', 'enabled', 'owner', 'subtree_memory',
    'type', 'domain', 'procs_errno', 'controllers', 'pids_enabled',
    'subtree_pids', 'tasks_max',
)
MEMORY_FIELDS = ('populated', 'cap', 'high', 'swap_max')


def structural(snapshot):
    """Ordered full tree; conditional controls exactly mirror scanner fields.

    pids.current is a checked observed count, not a control; its exact subtree
    count is independently validated in observe. Nothing is removed from scan.
    """
    return [tuple(r[k] for k in STRUCTURAL_FIELDS) +
            tuple(r.get(k) for k in MEMORY_FIELDS)
            for r in snapshot['rows']]


def collector(snapshot):
    """Explicit self binding required even prospectively and in synthetic input."""
    identity = snapshot['self_observation']
    pid, start = uint(identity['pid']), uint(identity['starttime'])
    unified, path = identity['unified_path'], identity['path']
    if not unified.startswith('/') or str(PurePosixPath(unified)) != unified or '..' in PurePosixPath(unified).parts:
        raise ValueError('noncanonical collector unified path')
    if path != '/sys/fs/cgroup'+('' if unified == '/' else unified):
        raise ValueError('collector path differs from unified path')
    row = next(r for r in snapshot['rows'] if r['path'] == path)
    if not pid or pid not in row['procs'] or dict(tid=pid, tgid=pid, starttime=start) not in row['identities']:
        raise ValueError('collector PID/starttime absent from validated membership')
    return dict(pid=pid, starttime=start, unified_path=unified, path=path)


def differences(before, after):
    """Preserve all raw membership and observed task-count deltas."""
    keys = ('procs', 'threads', 'identities', 'pids_current')
    return [dict(path=x['path'], fields={k: dict(before=x[k], after=y[k])
                for k in keys if x[k] != y[k]})
            for x, y in zip(before['rows'], after['rows'])
            if any(x[k] != y[k] for k in keys)]


def evaluate(old, before, after, requested, *, phase, expected=None, expected_unit=None):
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
        if phase == 'prospective' and (requested == 0 or expected is not None or expected_unit is not None):
            raise ValueError('prospective requires positive additional reservation and no scope declaration')
        if phase == 'inside-scope':
            if requested != 0:
                raise ValueError('inside-scope GO requires zero additional bytes')
            first = bind_scope(before, expected)
            second = bind_scope(after, expected)
            if first != second:
                raise ValueError('self scope identity/control race')
            if not isinstance(expected_unit, str) or not expected_unit.endswith('.scope') or PurePosixPath(expected_unit).name != expected_unit:
                raise ValueError('missing/invalid expected scope unit')
            if PurePosixPath(first['self_identity']['path']).name != expected_unit:
                raise ValueError('self scope unit differs from explicit expectation')
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
        a, b = observe(before), observe(after)
        first_self, second_self = collector(before), collector(after)
        if first_self != second_self:
            raise ValueError('collector identity/membership race')
        if structural(before) != structural(after):
            raise ValueError('hierarchy/structural/control race')
        out['collector_identity'] = first_self
        out['membership_differences'] = differences(before, after)
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
    raise RuntimeError('ResourceStability offline-only; live boundary DISABLED')
