#!/usr/bin/env python3
"""UNADOPTED read-only estimate. Never allocates a scope or launches a consumer.

Retains legacy visibility errors/cap denials; changes only resource estimation.
The two snapshots are not atomic or a scheduler lock. Credit is an estimate,
not a reclaim guarantee. This program is intentionally fail-closed.
"""
import datetime
import hashlib
import json
import os
from pathlib import Path
import resource
import subprocess
import time

GIB = 2**30
LIMIT = 55 * GIB
U64 = 2**64 - 1
REQUIRED = ('inactive_file', 'active_file', 'slab_reclaimable', 'slab_unreclaimable', 'anon', 'kernel')


def uint(value):
    if type(value) is not int or not 0 <= value <= U64:
        raise ValueError('invalid/overflow unsigned quantity')
    return value


def add(values):
    return uint(sum(uint(v) for v in values))


def parse_number(raw, allow_max=False):
    s = raw.strip()
    if s == 'max' and allow_max:
        return None
    if not s.isascii() or not s.isdecimal():
        raise ValueError('invalid numeric interface')
    return uint(int(s))


def pairs(raw):
    out = {}
    for line in raw.splitlines():
        key, val = line.split()
        if key in out:
            raise ValueError('duplicate stat field')
        out[key] = parse_number(val)
    return out


def scan(root=Path('/sys/fs/cgroup')):
    """Read every hierarchy node; controller-disabled usage stays at owner.

    The root has no memory.current: physical used minus top accounted currents
    is retained in full, including root tasks, uncharged kernel and VM overhead.
    No slab or inactive-file credit is taken on that residual.
    """
    raw = {}

    def read(path):
        content = path.read_text()
        raw[str(path)] = content
        return content

    mem = {}
    for line in read(Path('/proc/meminfo')).splitlines():
        key, rest = line.split(':', 1)
        if rest.strip().endswith(' kB'):
            mem[key] = uint(parse_number(rest.split()[0]) * 1024)
    rows = []

    def visit(path, enabled, owner, pids_enabled=False):
        with os.scandir(path) as entries:
            children = sorted(Path(e.path) for e in entries if e.is_dir(follow_symlinks=False))
        subtree = read(path/'cgroup.subtree_control').split()
        # cgroup.procs is read even for root and disabled subtrees, without RSS
        # summation (RSS double-counts shared pages and omits kernel charges).
        procs = [parse_number(x) for x in read(path/'cgroup.procs').split()]
        row = dict(path=str(path), parent=None if path == root else str(path.parent),
                   enabled=enabled, owner=owner, subtree_memory='memory' in subtree,
                   procs=procs, root=path == root,
                   pids_enabled=pids_enabled, subtree_pids='pids' in subtree)
        if path != root:
            events = pairs(read(path/'cgroup.events'))
            if events.get('populated') not in (0, 1):
                raise ValueError('missing/invalid populated')
            row['populated'] = bool(events['populated'])
        if enabled:
            row.update(current=parse_number(read(path/'memory.current')),
                       cap=parse_number(read(path/'memory.max'), True),
                       high=parse_number(read(path/'memory.high'), True),
                       swap_max=parse_number(read(path/'memory.swap.max'), True),
                       swap_current=parse_number(read(path/'memory.swap.current')),
                       tasks_max=parse_number(read(path/'pids.max'), True) if pids_enabled else None,
                       stat=pairs(read(path/'memory.stat')))
            owner = str(path)
        elif path != root and row['subtree_memory']:
            raise ValueError('memory enabled below disabled parent')
        rows.append(row)
        for child in children:
            visit(child, row['subtree_memory'], owner, row['subtree_pids'])
    try:
        visit(root, False, str(root))
    except (OSError, ValueError) as exc:
        exc.partial_raw_inputs = raw
        raise
    return dict(rows=rows, meminfo=mem, raw_inputs=raw,
                raw_sha256={k: hashlib.sha256(v.encode()).hexdigest() for k, v in raw.items()})


def accounting(snapshot):
    rows = snapshot['rows']
    by = {r['path']: r for r in rows}
    if len(by) != len(rows) or not rows or not rows[0]['root']:
        raise ValueError('duplicate/missing root')
    root = rows[0]
    if root['parent'] is not None:
        raise ValueError('root parent')
    for r in rows[1:]:
        parent = by[r['parent']]
        if r['enabled'] != parent['subtree_memory']:
            raise ValueError('controller coverage mismatch')
        expected_owner = parent['path'] if parent['enabled'] else parent['owner']
        if r['owner'] != expected_owner:
            raise ValueError('unknown disabled-subtree owner')
        if not r['enabled'] and r['subtree_memory']:
            raise ValueError('disabled subtree re-enables memory')
        if r['procs'] and not r['populated']:
            raise ValueError('direct tasks in empty group')
        if r['populated'] and not parent['root'] and not parent['populated']:
            raise ValueError('population race')
    frontier = []
    details = []
    for r in rows[1:]:
        if not r['enabled']:
            continue
        current = uint(r['current'])
        cap = r['cap']
        if cap is not None:
            uint(cap)
        for k in ('high', 'swap_max', 'tasks_max'):
            if r[k] is not None:
                uint(r[k])
        uint(r['swap_current'])
        for k in REQUIRED:
            uint(r['stat'][k])
        children = [c for c in rows if c['parent'] == r['path'] and c['enabled']]
        usage = current - add(c['current'] for c in children)
        uint(usage)
        ex = {k: r['stat'][k] - add(c['stat'][k] for c in children) for k in REQUIRED}
        for value in ex.values():
            uint(value)
            if value > usage:
                raise ValueError('exclusive component exceeds current')
        # Disjoint reclaimable categories must not exceed exclusive usage;
        # kernel includes slab, so never add kernel + slab as disjoint totals.
        if add((ex['inactive_file'], ex['active_file'], ex['anon'], ex['kernel'])) > usage:
            raise ValueError('inconsistent exclusive stat/current snapshot')
        if add((ex['slab_reclaimable'], ex['slab_unreclaimable'])) > ex['kernel']:
            raise ValueError('slab exceeds exclusive kernel')
        covering = next((p for p in frontier if r['path'].startswith(p['path']+'/')), None)
        if covering is None and r['populated'] and cap is not None:
            frontier.append(r)
            covering = r
        if cap is not None and current > cap:
            # Transient over-limit accounting cannot be silently covered by cap.
            raise ValueError('current exceeds finite cap')
        credit = add((ex['inactive_file'], ex['slab_reclaimable']//2)) if covering is None else 0
        if credit > usage:
            raise ValueError('overlapping credit')
        details.append(dict(path=r['path'], populated=r['populated'], cap=cap,
                            covered_by=covering['path'] if covering else None,
                            exclusive_current=usage, exclusive_stat=ex,
                            inactive_file_credit=ex['inactive_file'] if covering is None else 0,
                            half_slab_credit=ex['slab_reclaimable']//2 if covering is None else 0,
                            reserve=usage-credit if covering is None else 0))
    mem = snapshot['meminfo']
    total, free, available = (uint(mem[k]) for k in ('MemTotal', 'MemFree', 'MemAvailable'))
    if free > total or available > total:
        raise ValueError('invalid global memory snapshot')
    top = [r for r in rows if r['enabled'] and r['owner'] == root['path']]
    root_residual = total - free - add(r['current'] for r in top)
    uint(root_residual)
    bounded = add(r['cap'] for r in frontier)
    uncovered = add(d['reserve'] for d in details)
    return dict(frontier=[r['path'] for r in frontier], bounded_reserved_bytes=bounded,
                uncovered_reserve_bytes=uncovered, root_residual_bytes=root_residual,
                root_direct_pids=root['procs'], exclusive=details,
                half_slab_credit_bytes=add(d['half_slab_credit'] for d in details),
                inactive_file_credit_bytes=add(d['inactive_file_credit'] for d in details),
                disabled_coverage=[dict(path=r['path'], owner=r['owner'], procs=r['procs'])
                                   for r in rows[1:] if not r['enabled']],
                mem_total=total, mem_available=available)


def membership(snapshot):
    return [(r['path'], r['parent'], r['enabled'], r['owner'], r['subtree_memory'],
             r.get('populated'), r.get('cap'), r.get('high'), r.get('swap_max'),
             r.get('tasks_max'), r.get('pids_enabled'), r.get('subtree_pids'), tuple(r['procs'])) for r in snapshot['rows']]


def propose(old, before, after, requested):
    out = dict(schema='ResourceSlab20261024-proposal-v1', adopted=False,
               allowed=False, legacy=old, requested_bytes=requested,
               os_control_bytes=7*GIB, safe_limit_bytes=LIMIT,
               required_consumer_scope=dict(MemoryHigh='6G', MemoryMax='8G',
                    MemorySwapMax=0, TasksMax=64, stricter_existing='5G/7G unchanged'),
               print_axioms='N/A; formal budget ZERO')
    try:
        uint(requested)
        if requested == 0:
            raise ValueError('request must be positive')
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
        # component inconsistent within either scan already denies above.
        envelope = []
        for x, y in zip(a['exclusive'], b['exclusive']):
            if x['covered_by'] is None:
                usage = max(x['exclusive_current'], y['exclusive_current'])
                inactive = min(x['inactive_file_credit'], y['inactive_file_credit'])
                slab = min(x['half_slab_credit'], y['half_slab_credit'])
                envelope.append(dict(path=x['path'], usage=usage, inactive_credit=inactive,
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
    except (KeyError, TypeError, ValueError, OverflowError) as error:
        out['error'] = f'{type(error).__name__}: {error}'
    return out


def live(legacy_admission, source_hashes):
    start = time.monotonic()
    before = after = old = None
    error = None
    partial_raw = None
    try:
        old = legacy_admission(requested=4*GIB)
        before = scan()
        # Legacy helper supplies unchanged full process/service/Docker visibility.
        after = scan()
    except (OSError, ValueError, subprocess.SubprocessError) as exc:
        error = str(exc)
        partial_raw = getattr(exc, 'partial_raw_inputs', None)
    decisions = {}
    for size in (1, 2, 3, 4, 6, 7, 8):
        # Preserve the one measured legacy snapshot, algebraically re-evaluate
        # its documented inequalities for each request (no additional scan).
        legacy = dict(old or {})
        if old and 'bounded_reserved_bytes' in old and 'meminfo' in old and 'uncapped_resident_reserve_bytes' in old:
            requested = size*GIB
            legacy['requested_bytes'] = requested
            legacy['projected_reserved_bytes'] = old['bounded_reserved_bytes']+requested
            legacy['reserve_check'] = (legacy['projected_reserved_bytes']+old['uncapped_resident_reserve_bytes']+7*GIB < old['meminfo']['MemTotal'] and old['meminfo']['MemAvailable'] > requested+2*GIB)
            legacy['allowed'] = (not old.get('error') and not old.get('visibility_error') and legacy['projected_reserved_bytes'] < LIMIT and legacy['reserve_check'])
        decisions[str(size)] = propose(legacy, before, after, size*GIB)
    usage = resource.getrusage(resource.RUSAGE_SELF)
    return dict(utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),
                source_hashes=source_hashes, uname=os.uname().release,
                mode='READONLY PROPOSAL; no allocation, lock, consumer or adoption',
                snapshots=dict(before=before, after=after), original_legacy=old,
                decisions=decisions, collection_error=error, partial_raw_inputs=partial_raw,
                wall_seconds=time.monotonic()-start, peak_rss_kib=usage.ru_maxrss,
                swaps=usage.ru_nswap, exit=0, print_axioms='N/A; formal budget ZERO')
