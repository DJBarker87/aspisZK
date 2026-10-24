#!/usr/bin/env python3
"""ResourceHierarchy UNADOPTED read-only estimate. Derived from immutable 25b0b9df48.

Copied from pinned HEAD 5756082d85e4d6784de4566059d6a9845604342a ResourceStat.
Explicit derived-negative-stat exception: see ResourceHierarchy CRITERIA.md.
No cross-interface atomicity or future-memory guarantee.
Never allocates a scope or launches a consumer.

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

LINUX_EOPNOTSUPP = 95  # target Linux ABI, independent of synthetic-test host
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

    attempts = []

    def read(path):
        try:
            content = path.read_text()
        except OSError as exc:
            attempts.append(dict(path=str(path), errno=exc.errno, error=str(exc)))
            raise
        raw[str(path)] = content
        attempts.append(dict(path=str(path), errno=0, content=content,
                             sha256=hashlib.sha256(content.encode()).hexdigest()))
        return content

    def ids(value):
        result = [parse_number(x) for x in value.split()]
        if any(x == 0 for x in result) or len(set(result)) != len(result):
            raise ValueError('zero/duplicate membership identity')
        return sorted(result)

    def tag(path):
        try:
            return read(path/'cgroup.type').strip()
        except FileNotFoundError:
            if path != root:
                raise
            return 'root-special-domain'  # documented absent root interface

    rows = []
    mem = {}

    def visit(path, enabled, owner, pids_enabled=False, domain=None):
        kind = tag(path)  # MUST precede procs; no inferred threaded tag
        if kind not in ('domain', 'domain threaded', 'threaded', 'root-special-domain'):
            raise ValueError('invalid/unknown cgroup.type: '+kind)
        if path != root and kind == 'root-special-domain':
            raise ValueError('nonroot special domain')
        with os.scandir(path) as entries:
            children = sorted(Path(e.path) for e in entries if e.is_dir(follow_symlinks=False))
        subtree = read(path/'cgroup.subtree_control').split()
        controllers = read(path/'cgroup.controllers').split()
        if not set(subtree) <= set(controllers):
            raise ValueError('delegation not available')
        if kind == 'threaded':
            if domain is None or enabled or 'memory' in subtree or 'memory' in controllers:
                raise ValueError('threaded memory/domain owner mismatch')
        else:
            domain = str(path)
        threads = ids(read(path/'cgroup.threads'))
        procs_errno = 0
        try:
            procs = ids(read(path/'cgroup.procs'))
            if kind == 'threaded':
                raise ValueError('threaded procs unexpectedly readable/type race')
        except OSError as exc:
            if kind != 'threaded' or exc.errno != LINUX_EOPNOTSUPP:
                raise
            procs, procs_errno = [], exc.errno
        identities = []
        for tid in threads:
            proc = Path('/proc')/str(tid)
            first = read(proc/'stat')
            status = read(proc/'status')
            groups = read(proc/'cgroup')
            second = read(proc/'stat')
            def identity(value):
                # comm can contain spaces and parentheses; field 22 starttime.
                prefix, tail = value.rsplit(')', 1)
                return (parse_number(prefix.split(' ', 1)[0]),
                        parse_number(tail.split()[19]))
            if identity(first) != identity(second) or identity(first)[0] != tid:
                raise ValueError('thread identity changed')
            fields = dict(line.split(':', 1) for line in status.splitlines())
            tgid = parse_number(fields['Tgid'].strip())
            if parse_number(fields['Pid'].strip()) != tid or not tgid:
                raise ValueError('thread status identity mismatch')
            expected = '/' if path == root else '/'+str(path.relative_to(root))
            if [v[3:] for v in groups.splitlines() if v.startswith('0::')] != [expected]:
                raise ValueError('thread unified membership changed')
            identities.append(dict(tid=tid, tgid=tgid, starttime=identity(first)[1]))
        row = dict(path=str(path), parent=None if path == root else str(path.parent),
                   enabled=enabled, owner=owner, subtree_memory='memory' in subtree,
                   procs=procs, root=path == root, type=kind, domain=domain,
                   threads=threads, identities=identities, procs_errno=procs_errno,
                   controllers=controllers,
                   pids_enabled=pids_enabled, subtree_pids='pids' in subtree,
                   tasks_max=parse_number(read(path/'pids.max'), True) if pids_enabled else None,
                   pids_current=parse_number(read(path/'pids.current')) if pids_enabled else None)
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
                       stat=pairs(read(path/'memory.stat')))
            owner = str(path)
        elif path != root and row['subtree_memory']:
            raise ValueError('memory enabled below disabled parent')
        rows.append(row)
        for child in children:
            visit(child, row['subtree_memory'], owner, row['subtree_pids'],
                  domain if path == root or kind in ('threaded', 'domain threaded') else None)
        if tag(path) != kind:
            raise ValueError('cgroup.type transition')
    try:
        for line in read(Path('/proc/meminfo')).splitlines():
            key, rest = line.split(':', 1)
            if rest.strip().endswith(' kB'):
                mem[key] = uint(parse_number(rest.split()[0]) * 1024)
        visit(root, False, str(root))
        result = dict(rows=rows, meminfo=mem, raw_inputs=raw, read_attempts=attempts,
                      raw_sha256={k: hashlib.sha256(v.encode()).hexdigest() for k, v in raw.items()})
        validate_membership(result)
        return result
    except (OSError, ValueError, KeyError, IndexError) as exc:
        exc.partial_raw_inputs = raw
        exc.read_attempts = attempts
        raise


def validate_membership(snapshot):
    rows = snapshot['rows']
    by = {r['path']: r for r in rows}
    seen = set()
    for r in rows:
        kind = r['type']
        if kind not in ('domain', 'domain threaded', 'threaded', 'root-special-domain'):
            raise ValueError('unknown/invalid domain')
        if (kind == 'root-special-domain' and not r['root']) or (r['root'] and kind == 'threaded'):
            raise ValueError('root type mismatch')
        parent = by[r['parent']] if not r['root'] else None
        expected_domain = parent['domain'] if kind == 'threaded' else r['path']
        if r['domain'] != expected_domain:
            raise ValueError('incorrect threaded domain owner')
        if kind == 'threaded':
            if not parent['root'] and parent['type'] not in ('threaded', 'domain threaded'):
                raise ValueError('invalid threaded parent')
            if r['enabled'] or r['subtree_memory'] or 'memory' in r['controllers'] or r['procs_errno'] != LINUX_EOPNOTSUPP or r['procs']:
                raise ValueError('invalid threaded memory/procs semantics')
        elif r['procs_errno']:
            raise ValueError('nonthreaded unsupported procs')
        if parent and parent['type'] in ('threaded', 'domain threaded') and kind != 'threaded':
            raise ValueError('domain below threaded parent')
        if parent and r['pids_enabled'] != parent['subtree_pids']:
            raise ValueError('pids delegation mismatch')
        if r['pids_enabled']:
            uint(r['pids_current'])
            if r['tasks_max'] is not None:
                uint(r['tasks_max'])
                if r['pids_current'] > r['tasks_max']:
                    raise ValueError('pids current exceeds finite cap')
            count = sum(len(c['threads']) for c in rows if c['path'] == r['path'] or c['path'].startswith(r['path']+'/'))
            if count != r['pids_current']:
                raise ValueError('pids membership/current mismatch')
        for i in r['identities']:
            if not uint(i['tid']) or not uint(i['tgid']):
                raise ValueError('zero thread/process identity')
            uint(i['starttime'])
        if r['threads'] != sorted(i['tid'] for i in r['identities']):
            raise ValueError('incomplete thread identities')
        if seen.intersection(r['threads']):
            raise ValueError('duplicate thread across cgroups')
        seen.update(r['threads'])
        if not r['root'] and (r['threads'] or r['procs']) and not r['populated']:
            raise ValueError('live membership in empty node')
        if kind != 'threaded':
            tgids = {i['tgid'] for c in rows if c['domain'] == r['path'] for i in c['identities']}
            if tgids != set(r['procs']):
                raise ValueError('incomplete domain process/thread membership')


def accounting(snapshot):
    validate_membership(snapshot)
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
        # Raw inputs above remain unsigned. Only this derived vector is signed.
        for value in ex.values():
            if value > usage:
                raise ValueError('exclusive component exceeds current')
        # Historical "disjoint" label: LRU and type counters can overlap.
        # Kernel includes slab; never add kernel and slab in this total.
        negative = {k: -v for k, v in ex.items() if v < 0}
        debt = add(negative.values())
        positive_sum = add(max(0, ex[k]) for k in ('inactive_file', 'active_file', 'anon', 'kernel'))
        disjoint = positive_sum  # historical label; signed vector retained separately
        fallback = bool(negative) or positive_sum > usage
        add(max(0, ex[k]) for k in ('slab_reclaimable', 'slab_unreclaimable'))
        if ex['slab_reclaimable'] + ex['slab_unreclaimable'] > ex['kernel']:
            raise ValueError('slab exceeds exclusive kernel')
        covering = next((p for p in frontier if r['path'].startswith(p['path']+'/')), None)
        if covering is None and r['populated'] and cap is not None:
            frontier.append(r)
            covering = r
        if cap is not None and current > cap:
            # Transient over-limit accounting cannot be silently covered by cap.
            raise ValueError('current exceeds finite cap')
        if fallback and covering is not None:
            raise ValueError('inconsistent covered exclusive stat/current snapshot')
        charge = add((max(usage, positive_sum), debt)) if fallback else usage
        credit = add((ex['inactive_file'], ex['slab_reclaimable']//2)) if covering is None and not fallback else 0
        if credit > usage:
            raise ValueError('overlapping credit')
        details.append(dict(path=r['path'], populated=r['populated'], cap=cap,
                            covered_by=covering['path'] if covering else None,
                            exclusive_current=usage, exclusive_stat=ex,
                            disjoint_total=disjoint, fallback=fallback,
                            positive_sum=positive_sum, negative_debt=debt,
                            negative_components=negative, padding=charge-usage,
                            failure_provenance=('ResourceStat derived uint rejection' if negative else
                                                'ResourceStat positive-sum fallback' if fallback else None),
                            raw_values=dict(parent=dict(current=current, stat=dict(r['stat'])),
                                children=[dict(path=c['path'], current=c['current'], stat=dict(c['stat'])) for c in children]),
                            excess_over_current=max(0, disjoint-usage), conservative_charge=charge,
                            inactive_file_credit=ex['inactive_file'] if covering is None and not fallback else 0,
                            half_slab_credit=ex['slab_reclaimable']//2 if covering is None and not fallback else 0,
                            reserve=charge-credit if covering is None else 0))
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
             r.get('tasks_max'), r.get('pids_enabled'), r.get('subtree_pids'), tuple(r['procs']), r['type'], r['domain'], tuple(r['threads']),
             tuple((i['tid'], i['tgid'], i['starttime']) for i in r['identities']),
             r['procs_errno'], tuple(r['controllers'])) for r in snapshot['rows']]


def propose(old, before, after, requested):
    out = dict(schema='ResourceHierarchy20261024-proposal-v1', adopted=False,
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
    except (KeyError, TypeError, ValueError, OverflowError) as error:
        out['error'] = f'{type(error).__name__}: {error}'
    return out


def live(legacy_admission, source_hashes):
    start = time.monotonic()
    before = after = old = None
    error = None
    partial_raw = None
    attempts = None
    failures = {}
    snapshots = {}
    try:
        old = legacy_admission(requested=4*GIB)
    except (OSError, ValueError, subprocess.SubprocessError) as exc:
        failures['legacy'] = dict(error=str(exc))
    for phase in ('before', 'after'):
        try:
            snapshots[phase] = scan()
        except (OSError, ValueError, KeyError, IndexError) as exc:
            snapshots[phase] = None
            failures[phase] = dict(error=str(exc), errno=getattr(exc, 'errno', None),
                raw_inputs=getattr(exc, 'partial_raw_inputs', None),
                read_attempts=getattr(exc, 'read_attempts', None))
    before, after = snapshots['before'], snapshots['after']
    error = '; '.join(phase+': '+value['error'] for phase,value in failures.items()) or None
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
                decisions=decisions, collection_error=error, partial_raw_inputs=partial_raw, failed_read_attempts=attempts, failures=failures,
                wall_seconds=time.monotonic()-start, peak_rss_kib=usage.ru_maxrss,
                swaps=usage.ru_nswap, exit=0, print_axioms='N/A; formal budget ZERO')
