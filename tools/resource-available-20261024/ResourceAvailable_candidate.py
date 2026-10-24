"""ResourceAvailable v1 OFFLINE operator-policy candidate; never admission authority.
Scan and membership model copied from immutable entry HEAD ResourceHierarchy.
Signed correlations are diagnostics; raw observations remain strict uint64.
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
        seen_mem = set()
        for line in read(Path('/proc/meminfo')).splitlines():
            key, rest = line.split(':', 1)
            if key in seen_mem:
                raise ValueError('duplicate global field')
            seen_mem.add(key)
            words = rest.split()
            if len(words) not in (1,2) or (len(words)==2 and words[1]!='kB'):
                raise ValueError('invalid global unit/format')
            value = parse_number(words[0])
            if len(words)==2:
                mem[key] = uint(value * 1024)
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



def observe(snapshot):
    """Independent finite frontier plus global reserves; no old accounting()."""
    rows = snapshot['rows']
    if not rows or not rows[0]['root']:
        raise ValueError('missing root')
    by = {}
    root = rows[0]
    for n, r in enumerate(rows):
        path = r['path']
        from pathlib import PurePosixPath
        if not path.startswith('/') or str(PurePosixPath(path)) != path or '..' in PurePosixPath(path).parts or path in by:
            raise ValueError('duplicate/noncanonical tree path')
        for k in ('root', 'enabled', 'subtree_memory', 'pids_enabled', 'subtree_pids'):
            if type(r[k]) is not bool:
                raise ValueError('invalid tree flag')
        if n == 0:
            if r['parent'] is not None or r['enabled'] or r['owner'] != path:
                raise ValueError('invalid root')
        else:
            if r['root'] or r['parent'] not in by or str(PurePosixPath(path).parent) != r['parent']:
                raise ValueError('invalid tree parent/order')
            parent = by[r['parent']]
            if r['enabled'] != parent['subtree_memory']:
                raise ValueError('controller coverage mismatch')
            if r['owner'] != (parent['path'] if parent['enabled'] else parent['owner']):
                raise ValueError('unknown disabled-subtree owner')
            if not r['enabled'] and r['subtree_memory']:
                raise ValueError('disabled subtree re-enables memory')
            if type(r['populated']) is not bool:
                raise ValueError('invalid population')
            if r['populated'] and not parent['root'] and not parent['populated']:
                raise ValueError('population race')
        if len(r['controllers']) != len(set(r['controllers'])):
            raise ValueError('duplicate available controller')
        if r['subtree_memory'] and 'memory' not in r['controllers']:
            raise ValueError('memory delegation unavailable')
        if r['subtree_pids'] and 'pids' not in r['controllers']:
            raise ValueError('pids delegation unavailable')
        for key in ('procs', 'threads'):
            ids = r[key]
            if ids != sorted(set(ids)) or any(not uint(i) for i in ids):
                raise ValueError('invalid membership IDs')
        if r['enabled']:
            current = uint(r['current'])
            for k in ('cap', 'high', 'swap_max', 'tasks_max'):
                if r[k] is not None: uint(r[k])
            if r['cap'] is not None and current > r['cap']:
                raise ValueError('current exceeds finite cap')
            swap = uint(r['swap_current'])
            if r['swap_max'] is not None and swap > r['swap_max']:
                raise ValueError('swap current exceeds cap')
            for k in REQUIRED: uint(r['stat'][k])
            for value in r['stat'].values(): uint(value)
        by[path] = r
    validate_membership(snapshot)
    frontier = []
    diagnostics = []
    for r in rows[1:]:
        if not r['enabled']: continue
        covering = next((p for p in frontier if r['path'].startswith(p['path']+'/')), None)
        if covering is None and r['populated'] and r['cap'] is not None:
            frontier.append(r)
            covering = r
        children = [c for c in rows if c['parent'] == r['path'] and c['enabled']]
        # These differences and sums are signed mathematical diagnostics only.
        # All operands were checked above; no uint requirement on unused sums.
        usage = r['current'] - sum(c['current'] for c in children)
        ex = {k:r['stat'][k]-sum(c['stat'][k] for c in children) for k in REQUIRED}
        positive_sum = sum(max(0,ex[k]) for k in ('inactive_file','active_file','anon','kernel'))
        diagnostics.append(dict(path=r['path'], covered_by=covering['path'] if covering else None,
            exclusive_current=usage, exclusive_stat=ex, positive_type_lru_sum=positive_sum,
            negative_components={k:v for k,v in ex.items() if v<0},
            components_exceed_current={k:v for k,v in ex.items() if v>usage},
            slab_exceeds_kernel=ex['slab_reclaimable']+ex['slab_unreclaimable']>ex['kernel'],
            type_lru_overlap=positive_sum>usage,
            raw_values=dict(parent=dict(current=r['current'],stat=r['stat']),
                children=[dict(path=c['path'],current=c['current'],stat=c['stat']) for c in children])))
    mem = snapshot['meminfo']
    for value in mem.values(): uint(value)
    total = uint(mem['MemTotal'])
    for k in ('MemFree','MemAvailable','Active(file)','SReclaimable','KReclaimable'):
        if uint(mem[k]) > total: raise ValueError('global physical field exceeds MemTotal')
    if mem['KReclaimable'] < mem['SReclaimable']:
        raise ValueError('KReclaimable below SReclaimable')
    top = [r for r in rows if r['enabled'] and r['owner'] == root['path']]
    residual = uint(total-mem['MemFree']-add(r['current'] for r in top))
    return dict(frontier=[r['path'] for r in frontier],
        bounded_reserved_bytes=add(r['cap'] for r in frontier),
        root_residual_bytes=residual, mem_available=mem['MemAvailable'], mem_total=total,
        active_file_bytes=mem['Active(file)'],
        kernel_withheld_bytes=uint(mem['KReclaimable']-mem['SReclaimable']//2),
        diagnostics=diagnostics,root_direct_pids=root['procs'],
        disabled_coverage=[dict(path=r['path'],owner=r['owner'],procs=r['procs']) for r in rows[1:] if not r['enabled']])


def membership(snapshot):
    return [(r['path'], r['parent'], r['enabled'], r['owner'], r['subtree_memory'],
             r.get('populated'), r.get('cap'), r.get('high'), r.get('swap_max'),
             r.get('tasks_max'), r.get('pids_enabled'), r.get('subtree_pids'), tuple(r['procs']), r['type'], r['domain'], tuple(r['threads']),
             tuple((i['tid'], i['tgid'], i['starttime']) for i in r['identities']),
             r['procs_errno'], tuple(r['controllers'])) for r in snapshot['rows']]
