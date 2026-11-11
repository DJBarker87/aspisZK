#!/usr/bin/env python3
"""Aspis extraction probe: run Charon once from a spec. Runs INSIDE an fv_slot.sh scope (never directly).
Command line and environment are those of the PIN2 W8 runs (PW8_E002_spec.json / PW8_stage.py extract()); only the
launcher, the source payload and the paths differ. usage: XP_charon.py <spec.json>
spec: {run, pair: "second"|"first", crate: "verifier"|"program"|"pool", features, roots[], opaque[], include[], exclude[]?,
       overflow_checks: true|false, extra_charon[]?, src?: directory holding the workspace (default src)}"""
import hashlib, json, os, subprocess, sys, time
from pathlib import Path
E = Path(__file__).resolve().parent
spec = json.loads(Path(sys.argv[1]).read_text()); run = spec['run']
PAIRS = {
 'second': dict(dir='/home/dombarker/project-offloads/codex-pc-prov-p4x-20261110/PCWH_T004_out/bin',
                charon='57aa2359bb3e9a84480f7e4802dcdc700ef05709de30ec0eb97581b3f9c5f851',
                driver='6a6552bce70d59e041fb96a67c08294377ef16d3f77a7876fea7f1250ee37845'),
 'first': dict(dir='/home/dombarker/project-offloads/codex-cx-extraction-repro1-20261027/XRa_bin',
               charon='daad69bea1114042a2d2fbd3dfde99922b152d4f57023bf8edb83e5a6f336af8',
               driver='efdbe5b86c9f5f70c93810af08f358d4ecbaecf6f3e87517b1176689a8c28c45'),
}
P = PAIRS[spec['pair']]
sha = lambda p: hashlib.sha256(Path(p).read_bytes()).hexdigest()
assert sha(P['dir'] + '/charon') == P['charon'] and sha(P['dir'] + '/charon-driver') == P['driver'], 'tool hash mismatch'
src = E / spec.get('src', 'src')
manifest = {'verifier': 'crates/aspis-r1-cost-probe/Cargo.toml', 'program': 'programs/r1-cost-probe/Cargo.toml', 'pool': 'programs/aspis-pool/Cargo.toml'}[spec['crate']]
out = E / 'runs' / run; out.mkdir(parents=True, exist_ok=False)
llbc = out / 'out.llbc'
cmd = [P['dir'] + '/charon', 'cargo', '--preset', 'aeneas', '--mir', 'built', '--sysroot', 'default',
       '--include', 'core::option::Option', '--include', 'core::result::Result', '--include', 'core::option::_::ok_or']
for r in spec['roots']: cmd += ['--start-from', r]
for o in spec.get('opaque', []): cmd += ['--opaque', o]
for t in spec.get('include', []): cmd += ['--include', t]
for t in spec.get('exclude', []): cmd += ['--exclude', t]
cmd += spec.get('extra_charon', [])
cmd += ['--dest-file', str(llbc), '--', '--manifest-path', str(src / manifest), '--locked', '--offline', '--release', '--lib',
        '--jobs', '4', '--features', spec['features']]
env = {k: v for k, v in os.environ.items() if k not in ('RUSTFLAGS', 'RUSTC_WRAPPER', 'RUSTC_WORKSPACE_WRAPPER', 'CARGO_ENCODED_RUSTFLAGS', 'CHARON_TOOLCHAIN_IS_IN_PATH')}
env.update(PATH='/home/dombarker/.cargo/bin:/usr/bin:/bin', RUSTUP_TOOLCHAIN=spec.get('toolchain', 'nightly-2026-09-17'),
           CARGO_TARGET_DIR=str(E / 'target' / (spec['pair'] + '-' + spec['crate'] + ('' if spec.get('overflow_checks', True) else '-nochk'))),
           CARGO_NET_OFFLINE='true', CARGO_BUILD_JOBS='4', RAYON_NUM_THREADS='1', CARGO_PROFILE_RELEASE_CODEGEN_UNITS='2')
if spec.get('overflow_checks', True):
    env.update(RUSTFLAGS='-Zthreads=1 -C link-arg=-Wl,--threads=1 -C overflow-checks=yes', CARGO_PROFILE_RELEASE_OVERFLOW_CHECKS='true')
else:
    env.update(RUSTFLAGS='-Zthreads=1 -C link-arg=-Wl,--threads=1')
(out / 'spec.json').write_text(json.dumps(spec, indent=1) + '\n')
(out / 'charon_command.json').write_text(json.dumps(dict(command=cmd, env={k: env[k] for k in ('PATH', 'RUSTUP_TOOLCHAIN', 'CARGO_TARGET_DIR', 'CARGO_NET_OFFLINE', 'CARGO_BUILD_JOBS', 'RAYON_NUM_THREADS', 'CARGO_PROFILE_RELEASE_CODEGEN_UNITS', 'RUSTFLAGS') if k in env} | {'CARGO_PROFILE_RELEASE_OVERFLOW_CHECKS': env.get('CARGO_PROFILE_RELEASE_OVERFLOW_CHECKS')}), indent=1) + '\n')
lock = src / 'Cargo.lock'; lock_before = sha(lock)
t0 = time.time()
with open(out / 'charon.log', 'w') as log:
    r = subprocess.run(['/usr/bin/time', '-v', '-o', str(out / 'charon.time')] + cmd, cwd=src, env=env, stdout=log, stderr=subprocess.STDOUT)
res = dict(run=run, tool='charon', exit=r.returncode, wall_seconds=round(time.time() - t0, 2), lock_unchanged=(sha(lock) == lock_before),
           source_commit=(src / 'XP_SOURCE_COMMIT').read_text().strip() if (src / 'XP_SOURCE_COMMIT').exists() else spec.get('source_note'))
tim = (out / 'charon.time').read_text() if (out / 'charon.time').exists() else ''
for line in tim.splitlines():
    if 'Maximum resident set size' in line: res['peak_rss_kib'] = int(line.split(':')[1])
if llbc.exists():
    res['llbc_sha256'] = sha(llbc); res['llbc_bytes'] = llbc.stat().st_size
    doc = json.loads(llbc.read_text()); tr = doc.get('translated', doc)
    res['has_errors'] = doc.get('has_errors')
    decls = [f for f in tr.get('fun_decls', []) if f is not None]
    inv = []
    for f in decls:
        meta = f['item_meta']; name = meta['name']
        def el(x):
            if 'Ident' in x: return x['Ident'][0]
            if 'Impl' in x: return '{impl}'
            return '{' + next(iter(x)) + '}' if isinstance(x, dict) else str(x)
        body = f.get('body'); kind = (next(iter(body)) if isinstance(body, dict) else body)
        span = meta.get('span', {}); sp = span.get('data', span.get('span', span))
        inv.append(dict(id=f['def_id'], name='::'.join(el(x) for x in name), body=kind, opacity=meta.get('opacity'), is_local=meta.get('is_local'),
                        beg=(sp.get('beg') or {}).get('line') if isinstance(sp, dict) else None, end=(sp.get('end') or {}).get('line') if isinstance(sp, dict) else None))
    (out / 'declarations.json').write_text(json.dumps(inv, indent=0) + '\n')
    res['fun_decls'] = len(inv); res['types'] = len([t for t in tr.get('type_decls', []) if t is not None])
(out / 'charon_result.json').write_text(json.dumps(res, indent=1) + '\n')
print(json.dumps(res)); sys.exit(r.returncode)
