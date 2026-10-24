#!/usr/bin/env python3
"""Fail-closed cgroup-v2 hierarchical reservation admission (read-only).

A finite populated ancestor reserves its whole subtree once. Uncapped
background is visible by current usage, but is not invented as a reservation.
This is an instantaneous admission snapshot, not historical evidence or a
host-wide scheduler lock. Any missing/racing/unreadable necessary datum denies.
"""
from pathlib import Path
import argparse
import datetime
import hashlib
import json
import os

GIB = 2**30
LIMIT = 55 * GIB


def number(path):
    value = path.read_text().strip()
    if value == 'max':
        return None
    result = int(value)
    if result < 0:
        raise ValueError(f'negative cgroup value: {path}')
    return result


def inventory(root):
    rows = []

    def visit(path, covering=None, memory_enabled=True):
        # scandir propagates permission errors; pathlib.glob can suppress them.
        with os.scandir(path) as entries:
            children = sorted(Path(e.path) for e in entries if e.is_dir(follow_symlinks=False))
        is_root = path == root
        if is_root:
            # The unified hierarchy root has no memory.max or cgroup.events.
            row = dict(path=str(path), root=True, charged_bytes=0)
            rows.append(row)
        else:
            events = dict(line.split() for line in (path/'cgroup.events').read_text().splitlines())
            if events.get('populated') not in ('0', '1'):
                raise ValueError(f'missing/invalid hierarchical populated: {path}')
            populated = events['populated'] == '1'
            cap = number(path/'memory.max') if memory_enabled else None
            current = number(path/'memory.current') if memory_enabled else None
            if memory_enabled and current is None:
                raise ValueError(f'invalid current: {path}')
            row = dict(path=str(path), populated=populated,
                       memory_max=cap, memory_current=current,
                       memory_controller_enabled=memory_enabled,
                       memory_high=number(path/'memory.high') if memory_enabled else None,
                       memory_swap_max=number(path/'memory.swap.max') if memory_enabled else None,
                       covered_by=covering,
                       charged_bytes=cap if populated and cap is not None and covering is None else 0)
            rows.append(row)
            if populated and cap is not None and covering is None:
                covering = str(path)
        delegated_memory = 'memory' in (path/'cgroup.subtree_control').read_text().split()
        for child in children:
            visit(child, covering, delegated_memory)
        # Detect inconsistent snapshot: child alive while ancestor says empty.
        if not is_root and not row['populated']:
            if any(r.get('populated') and Path(r['path']).is_relative_to(path)
                   for r in rows if r is not row):
                raise ValueError(f'population changed during inventory: {path}')
    visit(root)
    return rows


def admission(root=Path('/sys/fs/cgroup'), requested=8*GIB):
    if requested < 0:
        raise ValueError('negative request')
    out = dict(schema='ProverRwNativeEntropy-reservation-v1',
               utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),
               requested_bytes=requested, safe_limit_bytes=LIMIT,
               scanner_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
               print_axioms='N/A: read-only resource gate', allowed=False)
    try:
        rows = inventory(root)
        total = sum(r['charged_bytes'] for r in rows)
        out.update(cgroups=rows, bounded_reserved_bytes=total,
                   projected_reserved_bytes=total+requested,
                   uncapped_background=[r for r in rows if r.get('populated') and
                                        r['memory_max'] is None and r['covered_by'] is None],
                   allowed=total+requested < LIMIT)
    except (OSError, ValueError) as error:
        out['error'] = f'{type(error).__name__}: {error}'
    return out


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('output', type=Path)
    parser.add_argument('--root', type=Path, default=Path('/sys/fs/cgroup'))
    parser.add_argument('--requested-bytes', type=int, default=8*GIB)
    args = parser.parse_args()
    out = admission(args.root, args.requested_bytes)
    args.output.write_text(json.dumps(out, indent=2)+'\n')
    print(json.dumps({k:v for k,v in out.items() if k not in ('cgroups','uncapped_background')}))
    raise SystemExit(0 if out['allowed'] else 78)


if __name__ == '__main__':
    main()
