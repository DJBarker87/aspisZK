#!/usr/bin/env python3
"""One focused Lean file, pinned cache, exclusive admission and capped receipt."""
import argparse, fcntl, hashlib, json, os, re, subprocess, time
from pathlib import Path

ap = argparse.ArgumentParser()
ap.add_argument('plan', type=Path)
a = ap.parse_args()
plan = json.loads(a.plan.read_text())
root = Path(plan['workspace'])
source = root / 'sources' / (plan['module'] + '.lean')
sha = lambda p: hashlib.sha256(p.read_bytes()).hexdigest()
assert sha(source) == plan['source_sha256']
assert '#print axioms' in source.read_text() or plan.get('audit_declarations')
assert not re.search(r'\b(sorry|admit)\b|(?m:^\s*axiom\s)', source.read_text())
cg = Path('/sys/fs/cgroup') / Path('/proc/self/cgroup').read_text().split('0::')[1].strip().lstrip('/')
limits = {n: (cg/n).read_text().strip() for n in ['memory.high', 'memory.max', 'memory.swap.max']}
assert limits == {'memory.high': str(6*2**30), 'memory.max': str(8*2**30), 'memory.swap.max': '0'}
with open('/tmp/aspis-r0-lean.lock', 'a+') as lock:
    fcntl.flock(lock, fcntl.LOCK_EX | fcntl.LOCK_NB)
    foreign = []
    for p in Path('/proc').iterdir():
        if not p.name.isdigit(): continue
        try:
            if (p/'comm').read_text().strip() in {'lean', 'lake'}:
                foreign.append(int(p.name))
        except OSError: pass
    assert not foreign, ('wait for idle Lean host', foreign)
    finite = []
    for p in Path('/sys/fs/cgroup').rglob('memory.max'):
        try:
            if p.read_text().strip() != 'max' and 'populated 1' in (p.parent/'cgroup.events').read_text():
                finite.append((str(p.parent), int(p.read_text())))
        except OSError: pass
    reservations = [(p,n) for p,n in finite if not any(p.startswith(q+'/') for q,_ in finite if q != p)]
    assert sum(n for _,n in reservations) <= 50*2**30, reservations
    env_file = Path('/home/dombarker/project-offloads/r1-privacy-build-integration-20261019/env/J.json')
    base = json.loads(env_file.read_text())
    env = dict(os.environ, **{k:v for k,v in base.items() if v is not None})
    env['LEAN_PATH'] = str(root/'objects') + ':/home/dombarker/project-offloads/aspis-joint-20261019/objects:' + base['LEAN_PATH']
    cache_provenance = None
    if plan.get('cache_receipt'):
        cache_path = Path(plan['cache_receipt']['path'])
        assert sha(cache_path) == plan['cache_receipt']['sha256']
        cached = json.loads(cache_path.read_text())
        assert cached['exit_status'] == 0 and cached['axioms']['passed']
        assert cached['source_manifest_entry']['source_sha256'] == plan['cache_target_source']['sha256']
        old_command = cached['command']
        assert '/home/dombarker/.elan/toolchains/leanprover--lean4---v4.32.0/bin/lean' in old_command
        old_lean = old_command.index('/home/dombarker/.elan/toolchains/leanprover--lean4---v4.32.0/bin/lean')
        old_roots = old_command[old_lean+1].split(':')
        assert all('4.31' not in value for value in old_roots)
        cache_objects = {}
        for name, item in cached['key']['imports'].items():
            pin = item['objects']['.olean']
            assert sha(Path(pin['path'])) == pin['sha256'], name
            cache_objects[name] = pin
        # A cached theorem's complete original closure takes priority over the
        # integration overlay. Mixing nominally equal module names silently
        # dropped verifier carriers from the original PublicPreparation module.
        original_roots = [value for value in old_roots if Path(value).is_dir()]
        current_roots = env['LEAN_PATH'].split(':')
        ordered = list(dict.fromkeys([str(root/'objects'), *original_roots, *current_roots]))
        env['LEAN_PATH'] = ':'.join(ordered)
        def resolve_object(name, roots):
            return next((Path(value)/(name.replace('.','/')+'.olean') for value in roots
                if (Path(value)/(name.replace('.','/')+'.olean')).is_file()), None)
        selected = {}
        for name,pin in {**cache_objects,cached['target']:cached['objects']['.olean']}.items():
            resolved = resolve_object(name,ordered)
            assert resolved is not None and sha(resolved) == pin['sha256'], ('cache shadow',name)
            selected[name] = dict(path=str(resolved),sha256=sha(resolved))
        owners = {}
        for name in ['AspisR1PublicPreparation.Types','AspisR1PublicPreparation.Funs','Aeneas']:
            original = resolve_object(name,original_roots)
            resolved = resolve_object(name,ordered)
            if original is not None:
                assert resolved is not None and sha(resolved) == sha(original), ('owner shadow',name)
                owners[name] = dict(path=str(resolved),sha256=sha(resolved))
        cache_provenance = dict(plan['cache_receipt'],target=cached['target'],
            validated_direct_import_objects=cache_objects,original_roots=original_roots,
            selected_cache_objects=selected,selected_owner_objects=owners,
            target_objects=cached['objects'],priority='NEW_CU_MODULES_THEN_EXACT_ORIGINAL_CLOSURE')
    imports = []
    for name in re.findall(r'(?m)^\s*(?:public\s+)?import\s+(\S+)', source.read_text()):
        candidates = [Path(p)/(name.replace('.','/')+'.olean') for p in env['LEAN_PATH'].split(':')]
        obj_import = next((p for p in candidates if p.is_file()), None)
        assert obj_import is not None, ('focused prerequisite missing; do not compile a dependent', name)
        if cache_provenance and name == cached['target']:
            assert sha(obj_import) == cached['objects']['.olean']['sha256'], name
        imports.append(dict(module=name,path=str(obj_import),sha256=sha(obj_import)))
    out = root/'runs'/plan['attempt']
    out.mkdir(parents=True, exist_ok=False)
    (root/'objects').mkdir(exist_ok=True)
    obj = root/'objects'/(plan['module']+'.olean')
    obj.parent.mkdir(parents=True, exist_ok=True)
    checked_source = source
    if plan.get('audit_declarations'):
        checked_source = root/'checked'/(plan['module']+'.lean')
        checked_source.parent.mkdir(parents=True, exist_ok=True)
        suffix = ''.join('\n#print axioms '+decl+'\n' for decl in plan['audit_declarations'])
        checked_source.write_text(source.read_text()+suffix)
    # Lake replaces LEAN_PATH. Restore the pinned overlay after entering its
    # environment; never build missing dependencies to discover a local error.
    command = [base['LAKE'], 'env', 'env', 'LEAN_PATH='+env['LEAN_PATH'], base['LEAN'],
        '--root='+str(root/('checked' if plan.get('audit_declarations') else 'sources')),
        '-M7000', '-o', str(obj), str(checked_source)]
    start = time.monotonic()
    before = Path('/proc/meminfo').read_text()
    with (out/'stdout.log').open('w') as log:
        p = subprocess.Popen(['/usr/bin/time', '-v', '-o', str(out/'time.log'), 'timeout', '600', *command],
            cwd=plan['lake_workspace'], env=env, stdout=log, stderr=subprocess.STDOUT)
        aggregate_peak = 0
        while p.poll() is None:
            rss = 0
            for pid in (cg/'cgroup.procs').read_text().split():
                try: rss += int(Path('/proc',pid,'statm').read_text().split()[1]) * os.sysconf('SC_PAGE_SIZE')
                except (OSError, IndexError): pass
            aggregate_peak = max(aggregate_peak, rss)
            time.sleep(.2)
        status = p.wait()
    timing = (out/'time.log').read_text()
    def metric(label):
        m = re.search(re.escape(label)+r':\s*(\d+)', timing)
        return int(m[1]) if m else None
    log = (out/'stdout.log').read_text()
    receipt = dict(plan, command=command, exit_status=status, wall_seconds=time.monotonic()-start,
        peak_rss_kib=metric('Maximum resident set size (kbytes)'), process_swaps=metric('Swaps'),
        aggregate_rss_peak_bytes=aggregate_peak, cgroup_limits=limits, reservations=reservations,
        cgroup_swap_bytes=int((cg/'memory.swap.current').read_text()),
        host_swap_before=[s for s in before.splitlines() if s.startswith('Swap')],
        host_swap_after=[s for s in Path('/proc/meminfo').read_text().splitlines() if s.startswith('Swap')],
        environment_sha256=sha(env_file), lean_path=env['LEAN_PATH'], runner_sha256=sha(Path(__file__)),
        checked_source_sha256=sha(checked_source),
        direct_imports=imports,cache_provenance=cache_provenance,
        print_axioms_output=log, object_sha256=sha(obj) if status==0 else None)
    (out/'receipt.json').write_text(json.dumps(receipt,indent=2)+'\n')
    print(json.dumps(receipt))
    raise SystemExit(status)
