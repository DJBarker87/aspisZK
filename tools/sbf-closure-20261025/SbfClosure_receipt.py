"""Small bounded receipt support; no host access, build or privilege operations."""
import hashlib, json, os, pathlib, resource, subprocess, sys, time, traceback, threading
ROOT = pathlib.Path(__file__).resolve().parents[2]
E = ROOT / 'evidence/sbf-closure-20261025'
T = ROOT / 'tools/sbf-closure-20261025'
LIMIT = 512 * 1024**2

def sha(data):
    return hashlib.sha256(data).hexdigest()

def pin(path):
    h = hashlib.sha256()
    with pathlib.Path(path).open('rb') as f:
        while b := f.read(1024**2):
            h.update(b)
    return {'bytes': pathlib.Path(path).stat().st_size, 'sha256': h.hexdigest()}

def git(*args):
    return subprocess.check_output(['git', *args], cwd=ROOT)

def write(name, value):
    data = (json.dumps(value, indent=2, sort_keys=True) + '\n').encode()
    if len(data) > 5_000_000:
        raise ValueError('derived JSON exceeds 5MB; retain hash/size only')
    with (E / name).open('xb') as f:
        f.write(data)
    return pin(E / name)

def run(name, action):
    # Darwin rejects RLIMIT_AS: data cap + sampled RSS guard, NOT hard total RSS.
    kind = resource.RLIMIT_DATA if sys.platform == 'darwin' else resource.RLIMIT_AS
    resource.setrlimit(kind, (LIMIT, LIMIT))
    if sys.platform == 'darwin':
        def guard():
            while True:
                if resource.getrusage(0).ru_maxrss >= 480*1024**2:
                    os._exit(125)
                time.sleep(0.01)
        threading.Thread(target=guard, daemon=True).start()
    os.umask(0o077)
    start = time.monotonic()
    r = {'command': [sys.executable, '-B', *sys.argv],
         'source_revision': git('rev-parse', 'HEAD').decode().strip(),
         'memory_limit_bytes': LIMIT,
         'memory_limit_kind': 'RLIMIT_DATA + sampled 480MiB RSS guard' if sys.platform == 'darwin' else 'RLIMIT_AS',
         'helpers': {p.name: pin(p) for p in sorted(T.glob('*.py'))},
         'interpreter': {'path': str(pathlib.Path(sys.executable).resolve()),
                         'version': sys.version, **pin(pathlib.Path(sys.executable).resolve())},
         'print_axioms': 'N/A: Python-only preparation, no formal theorem/import'}
    try:
        r['result'] = action()
        r['exit'] = 0
    except Exception as e:
        r.update(exit=1, error=repr(e), traceback=traceback.format_exc())
    u = resource.getrusage(resource.RUSAGE_SELF)
    c = resource.getrusage(resource.RUSAGE_CHILDREN)
    scale = 1 if sys.platform == 'darwin' else 1024
    r.update(wall_seconds=time.monotonic()-start, peak_rss_bytes=u.ru_maxrss*scale,
             child_peak_rss_bytes=c.ru_maxrss*scale, swap=u.ru_nswap+c.ru_nswap,
             metric_scope='process maxima, not aggregate; child maximum reported separately',
             runtime_modules={str(pathlib.Path(m.__file__).resolve()): pin(pathlib.Path(m.__file__).resolve())
                for m in list(sys.modules.values()) if getattr(m, '__file__', None)
                and pathlib.Path(m.__file__).is_file()})
    write(name, r)
    print(json.dumps({k:r[k] for k in ('exit','wall_seconds','peak_rss_bytes','swap')}))
    if r['exit']:
        print(r['traceback'], file=sys.stderr)
    return r['exit']
