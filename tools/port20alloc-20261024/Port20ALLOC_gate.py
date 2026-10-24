#!/usr/bin/env python3
"""Read-only, all-hierarchy admission. Missing/raced data denies admission.

Finite populated ancestors reserve once; inactive groups reserve nothing.
Uncapped process RSS is separate from hierarchical memory.current/page cache.
No service, cache or cgroup is mutated. Run twice immediately before launch.
"""
import hashlib, json, os, pathlib, sys, time

G = 1024**3
ROOT = pathlib.Path('/sys/fs/cgroup')

def hierarchy(root=ROOT):
    rows = []
    def visit(p, cover=None):
        rel = str(p.relative_to(root))
        events = dict(x.split() for x in (p/'cgroup.events').read_text().splitlines()) if p != root else {'populated':'1'}
        pop = int(events['populated'])
        assert pop in (0, 1)
        maximum = (p/'memory.max').read_text().strip() if (p/'memory.max').exists() else 'max'
        if p != root and 'memory' in (p.parent/'cgroup.subtree_control').read_text().split():
            assert (p/'memory.max').is_file(), rel
        cap = None if maximum == 'max' else int(maximum)
        row = dict(path=rel, populated=pop, maximum=maximum, covering_ancestor=cover)
        if cap is not None and pop and cover is None:
            assert cap > 0
            row['reservation_bytes'] = cap
            cover = rel
        row['effective_cover'] = cover
        # Read direct IDs even for groups with no memory controller.
        kind = (p/'cgroup.type').read_text().strip() if p != root else 'domain'
        row['direct_ids'] = (p/('cgroup.threads' if kind == 'threaded' else 'cgroup.procs')).read_text().split()
        if (p/'memory.current').exists():
            row['memory_current_diagnostic_only'] = int((p/'memory.current').read_text())
        rows.append(row)
        for child in sorted(p.iterdir()):
            if child.is_dir(): visit(child, cover)
    visit(root)
    return rows

def topology(rows):
    return [(r['path'], r['populated'], r['maximum'], r['covering_ancestor']) for r in rows]

def processes(rows):
    groups = {r['path']:r for r in rows}
    out = []
    for p in sorted(pathlib.Path('/proc').iterdir()):
        if not p.name.isdecimal(): continue
        # A disappearing process is a raced snapshot, not a zero-RSS process.
        stat = (p/'stat').read_text()
        start = stat[stat.rindex(')')+2:].split()[19]
        group = next(l[3:].lstrip('/') or '.' for l in (p/'cgroup').read_text().splitlines() if l.startswith('0::'))
        assert group in groups, (p.name, group)
        status = dict(l.split(':',1) for l in (p/'status').read_text().splitlines() if ':' in l)
        rss = int(status.get('VmRSS','0 kB').split()[0])*1024
        swap = int(status.get('VmSwap','0 kB').split()[0])*1024
        assert (p/'stat').read_text().split(')')[-1].split()[19] == start, p.name
        out.append(dict(pid=int(p.name), start=start, group=group, rss=rss, swap=swap,
                        capped=groups[group]['effective_cover'] is not None))
    return out

def snapshot():
    before = hierarchy()
    procs = processes(before)
    after = hierarchy()
    if topology(before) != topology(after):
        b={r[0]:r[1:] for r in topology(before)}
        a={r[0]:r[1:] for r in topology(after)}
        raise RuntimeError(json.dumps(dict(reason='cgroup topology/limits/population raced',
            changed={k:dict(before=b.get(k),after=a.get(k)) for k in b.keys()|a.keys() if b.get(k)!=a.get(k)})))
    # Check all directly listed IDs remain visible in /proc (including threads).
    for row in after:
        for pid in row['direct_ids']: assert pathlib.Path('/proc',pid,'status').is_file(), pid
    mem = {l.split(':')[0]:int(l.split()[1])*1024 for l in pathlib.Path('/proc/meminfo').read_text().splitlines() if l.split()[1].isdigit()}
    reserved = sum(r.get('reservation_bytes',0) for r in after)
    uncapped = sum(p['rss'] for p in procs if not p['capped'])
    # Shared RSS can overcount; never add parent/child memory.current values.
    admitted = reserved+2*G < 55*G and reserved+2*G+uncapped+6*G < mem['MemTotal'] and mem['MemAvailable'] >= 8*G
    return dict(schema='Port20ALLOC-admission-v1',timestamp=time.time(),pid=os.getpid(),
                all_cgroups=after,all_processes=procs,reserved_bytes=reserved,
                uncapped_rss_bytes=uncapped,os_reserve_bytes=6*G,new_bytes=2*G,
                meminfo=mem,admitted=admitted,print_axioms='N/A: read-only admission')

if __name__ == '__main__':
    try: result=snapshot()
    except Exception as e: result=dict(admitted=False,fail_closed=True,error=repr(e))
    print(json.dumps(result,indent=2))
    sys.exit(0 if result['admitted'] else 2)
