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
