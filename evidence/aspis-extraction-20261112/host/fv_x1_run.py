#!/usr/bin/env python3
"""X1: ONE linked translation of the deployed verifier program (frozen tree 3d700effcab). Runs INSIDE one fv_slot.sh
scope (started by fv_x1_emit.sh), never directly. A tool record: what the second tool pair (Charon 454586e9, Aeneas
0d21a9ec) translates and whether the emitted Lean elaborates against the R1 (L187) library. Nothing here is a proof.
usage: fv_x1_run.py <run config.json> <out dir>
The run config names everything: source tree, manifest, features, overflow-check setting, extra environment (the two
deployment program ids of the devnet build), Charon roots / include / opaque / exclude, Aeneas modes, the adaptation
rules and shims, and whether Lean runs. Steps:
  1 Charon (the workers' command line: --preset aeneas --mir built --sysroot default, the three Option/Result includes,
    cargo --locked --offline --release --lib --jobs 4), ONE run on the program crate with the library crates included;
  2 Aeneas for each mode listed (release = WITH -abort-on-error; noabort = without, to list every rejection);
  3 scans on the emission of the first mode that produced a Funs.lean: TP_llbc_scan.py over the four Aspis crates
    (completeness by span, mutable-borrow type arguments under an erased region), tp3_erased_scan.py, and a source
    search of the four crates for a reversed mutable iterator;
  4 Lean (if asked): TP_adapt.py with the run's rules, the shims compiled first, then the four modules one at a time
    with fv_x1_lean_one.sh against the L187 objects; TP_errmap.py on Funs."""
import hashlib, json, os, re, subprocess, sys, time
from pathlib import Path
B = Path(__file__).resolve().parent
WK = Path('/home/dombarker/project-offloads/future-version-20261111/frz-emit/bin/worker')   # the workers' tools, read only
CHARON_DIR = '/home/dombarker/project-offloads/codex-pc-prov-p4x-20261110/PCWH_T004_out/bin'
CHARON_SHA = '57aa2359bb3e9a84480f7e4802dcdc700ef05709de30ec0eb97581b3f9c5f851'
DRIVER_SHA = '6a6552bce70d59e041fb96a67c08294377ef16d3f77a7876fea7f1250ee37845'
AENEAS = CHARON_DIR + '/aeneas'
AENEAS_SHA = '230ee9f0c4902ea3415a01960f6887e2d4c71bc82e8b4e78dfac398da657df91'
MODS = ('TypesExternal', 'Types', 'FunsExternal', 'Funs')
sha = lambda p: hashlib.sha256(Path(p).read_bytes()).hexdigest()

def main():
    CFG, OUT = Path(sys.argv[1]), Path(sys.argv[2])
    cfg = json.loads(CFG.read_text()); SRC = Path(cfg['source'])
    for d in ('runs', 'lean-src', 'lean-out', 'summaries', 'flat'): (OUT / d).mkdir(parents=True, exist_ok=True)
    ST = OUT / 'steps.txt'
    def note(s):
        with open(ST, 'a') as f: f.write(s + '\n')
    def step(name, cmd, out_path, cwd=None, env=None):
        t0 = time.time()
        with open(out_path, 'w') as fo: rc = subprocess.run(cmd, stdout=fo, stderr=subprocess.STDOUT, cwd=cwd, env=env).returncode
        w = round(time.time() - t0, 1); note('%s exit %d; wall %s s' % (name, rc, w)); return rc, w
    def peak(timefile):
        try: return next((int(l.split(':')[1]) for l in Path(timefile).read_text().splitlines() if 'Maximum resident' in l), None)
        except FileNotFoundError: return None
    assert sha(CHARON_DIR + '/charon') == CHARON_SHA and sha(CHARON_DIR + '/charon-driver') == DRIVER_SHA and sha(AENEAS) == AENEAS_SHA, 'tool hash mismatch'
    (OUT / 'config.json').write_text(CFG.read_text())
    res = dict(source=str(SRC), frozen_commit=(SRC / 'FROZEN_COMMIT').read_text().strip() if (SRC / 'FROZEN_COMMIT').exists() else None,
               config_sha256=sha(CFG), charon_sha256=CHARON_SHA, charon_driver_sha256=DRIVER_SHA, aeneas_sha256=AENEAS_SHA,
               started=time.strftime('%Y-%m-%dT%H:%M:%SZ', time.gmtime()),
               worker_tools={p.name: sha(p) for p in sorted(WK.iterdir()) if p.is_file()}, bin={p.name: sha(p) for p in sorted(B.iterdir()) if p.is_file()})
    note('source %s; out %s; config sha256 %s' % (SRC, OUT, res['config_sha256']))
    def save(): json.dump(res, open(OUT / 'result.json', 'w'), indent=1)
    # ---------------- 1 Charon
    cdir = OUT / 'runs' / 'C'; cdir.mkdir(exist_ok=True); llbc = cdir / 'out.llbc'
    cmd = [CHARON_DIR + '/charon', 'cargo', '--preset', 'aeneas', '--mir', 'built', '--sysroot', 'default',
           '--include', 'core::option::Option', '--include', 'core::result::Result', '--include', 'core::option::_::ok_or']
    cmd += cfg.get('charon_extra_flags', [])
    for x in cfg['roots']: cmd += ['--start-from', x]
    for x in cfg.get('include', []): cmd += ['--include', x]
    for x in cfg.get('opaque', []): cmd += ['--opaque', x]
    for x in cfg.get('exclude', []): cmd += ['--exclude', x]
    cmd += ['--dest-file', str(llbc), '--', '--manifest-path', str(SRC / cfg['manifest']), '--locked', '--offline', '--release', '--lib', '--jobs', '4', '--features', cfg['features']]
    env = {k: v for k, v in os.environ.items() if k not in ('RUSTFLAGS', 'RUSTC_WRAPPER', 'RUSTC_WORKSPACE_WRAPPER', 'CARGO_ENCODED_RUSTFLAGS', 'CHARON_TOOLCHAIN_IS_IN_PATH', 'CARGO_PROFILE_RELEASE_OVERFLOW_CHECKS')}
    env.update(PATH='/home/dombarker/.cargo/bin:/usr/bin:/bin', RUSTUP_TOOLCHAIN='nightly-2026-09-17', CARGO_TARGET_DIR=cfg['cargo_target_dir'],
               CARGO_NET_OFFLINE='true', CARGO_BUILD_JOBS='4', RAYON_NUM_THREADS='1', CARGO_PROFILE_RELEASE_CODEGEN_UNITS='2')
    if cfg['overflow_checks']: env.update(RUSTFLAGS='-Zthreads=1 -C link-arg=-Wl,--threads=1 -C overflow-checks=yes', CARGO_PROFILE_RELEASE_OVERFLOW_CHECKS='true')
    else: env.update(RUSTFLAGS='-Zthreads=1 -C link-arg=-Wl,--threads=1', CARGO_PROFILE_RELEASE_OVERFLOW_CHECKS='false')
    env.update(cfg.get('extra_env', {}))
    keys = ('PATH', 'RUSTUP_TOOLCHAIN', 'CARGO_TARGET_DIR', 'CARGO_NET_OFFLINE', 'CARGO_BUILD_JOBS', 'RAYON_NUM_THREADS', 'CARGO_PROFILE_RELEASE_CODEGEN_UNITS',
            'RUSTFLAGS', 'CARGO_PROFILE_RELEASE_OVERFLOW_CHECKS') + tuple(cfg.get('extra_env', {}))
    (cdir / 'charon_command.json').write_text(json.dumps(dict(command=cmd, env={k: env.get(k) for k in keys}), indent=1) + '\n')
    lock0 = sha(SRC / 'Cargo.lock')
    rc, w = step('charon', ['/usr/bin/time', '-v', '-o', str(cdir / 'charon.time')] + cmd, cdir / 'charon.log', cwd=SRC, env=env)
    res['charon'] = dict(exit=rc, wall=w, lock_unchanged=sha(SRC / 'Cargo.lock') == lock0, peak_rss_kib=peak(cdir / 'charon.time'))
    save()
    if not llbc.exists():
        note('   charon produced no LLBC: ' + ' | '.join((cdir / 'charon.log').read_text(errors='replace').splitlines()[-6:])[:900]); note('DONE'); return
    res['charon']['llbc_sha256'] = sha(llbc)
    doc = json.loads(llbc.read_text()); tr = doc.get('translated', doc)
    res['charon']['fun_decls'] = len([f for f in tr.get('fun_decls', []) if f]); res['charon']['has_errors'] = doc.get('has_errors')
    note('   llbc sha256 %s; %d function declarations; charon exit %d' % (res['charon']['llbc_sha256'], res['charon']['fun_decls'], rc))
    del doc, tr
    save()
    # ---------------- 2 Aeneas
    ns = cfg['ns']; used = None
    for mode in cfg['aeneas_modes']:
        adir = OUT / 'runs' / ('A-' + mode); adir.mkdir(exist_ok=True)
        acmd = [AENEAS, '-diagnose-translation', '-sequential', '-no-progress-bar'] + (['-abort-on-error'] if mode == 'release' else []) + \
               cfg.get('aeneas_extra_flags', []) + ['-backend', 'lean', '-namespace', ns, '-dest', str(adir / 'raw'), '-subdir', ns, '-split-files', str(llbc)]
        (adir / 'aeneas_command.json').write_text(json.dumps(dict(command=acmd, llbc_sha256=sha(llbc)), indent=1) + '\n')
        rc, w = step('aeneas-' + mode, ['/usr/bin/time', '-v', '-o', str(adir / 'aeneas.time')] + acmd, adir / 'aeneas.log', cwd=adir)
        outs = {str(p.relative_to(adir)): sha(p) for p in sorted((adir / 'raw').rglob('*')) if p.is_file()} if (adir / 'raw').exists() else {}
        log = (adir / 'aeneas.log').read_text(errors='replace')
        res['aeneas_' + mode] = dict(exit=rc, wall=w, error_lines=log.count('[Error]'), peak_rss_kib=peak(adir / 'aeneas.time'), outputs=outs)
        note('   aeneas %s: exit %d, [Error] lines %d' % (mode, rc, log.count('[Error]')))
        if used is None and (adir / 'raw' / ns / 'Funs.lean').exists(): used = (adir, mode)
        save()
    if used is None: note('   no Funs.lean emitted'); note('DONE'); return
    adir, mode = used; raw = adir / 'raw' / ns; res['emission_used'] = mode
    # ---------------- 3 scans
    crates = cfg['crates']
    step('scan', [sys.executable, '-I', str(WK / 'TP_llbc_scan.py'), str(cdir), str(raw), str(OUT / 'summaries' / 'scan.json')] + [c + '::' for c in crates], OUT / 'summaries' / 'scan.txt')
    for c in crates:
        step('erased-' + c, [sys.executable, '-I', str(WK / 'tp3_erased_scan.py'), str(llbc), str(raw / 'Funs.lean'), c], OUT / 'summaries' / ('erased-%s.json' % c))
    hits = []
    for d in cfg['crate_dirs']:
        for p in sorted((SRC / d).rglob('*.rs')):
            t = p.read_text(errors='replace')
            for m in re.finditer(r'\b(iter_mut|chunks_mut|chunks_exact_mut|rchunks_mut|split_at_mut|values_mut)\s*\([^;{}]*?\)\s*(?:\.\s*\w+\s*\([^;{}]*?\)\s*)*\.\s*rev\s*\(\s*\)', t):
                hits.append('%s:%d' % (p.relative_to(SRC), t.count('\n', 0, m.start()) + 1))
    res['reversed_mutable_iterator_sites'] = hits; save()
    if not cfg.get('lean'): note('DONE'); return
    # ---------------- 4 Lean
    for s in cfg['shims']:
        (OUT / 'lean-src' / (s + '.lean')).write_bytes(Path(cfg.get('shim_dirs', {}).get(s, cfg['shim_dir']), s + '.lean').read_bytes())
        rc, w = step('lean-shim-' + s, ['bash', str(B / 'fv_x1_lean_one.sh'), str(OUT), s, '300'], OUT / 'summaries' / ('lean-' + s + '.log'))
        res.setdefault('shims', {})[s] = dict(sha256=sha(OUT / 'lean-src' / (s + '.lean')), exit=rc, wall=w)
    pre = cfg['prefix']
    step('adapt', [sys.executable, '-I', str(WK / 'TP_adapt.py'), str(raw), ns, pre, str(OUT / 'flat' / pre), cfg['rules']], OUT / 'summaries' / 'adapt.json')
    for p in sorted((OUT / 'flat' / pre).glob('*.lean')): (OUT / 'lean-src' / p.name).write_bytes(p.read_bytes())
    res['lean'] = {}
    for M in MODS:
        if not (OUT / 'lean-src' / (pre + M + '.lean')).exists(): res['lean'][M] = 'absent'; continue
        logp = OUT / 'summaries' / ('lean-%s%s.log' % (pre, M))
        rc, w = step('lean-' + pre + M, ['/usr/bin/time', '-v', '-o', str(OUT / 'summaries' / ('lean-%s%s.time' % (pre, M))), 'bash', str(B / 'fv_x1_lean_one.sh'), str(OUT), pre + M, str(cfg.get('lean_timeout', 1800))], logp)
        n = len(re.findall(r': error', logp.read_text(errors='replace')))
        res['lean'][M] = dict(exit=rc, wall=w, errors=n, sha256=sha(OUT / 'lean-src' / (pre + M + '.lean')), peak_rss_kib=peak(OUT / 'summaries' / ('lean-%s%s.time' % (pre, M))))
        note('   errors in %s%s: %d' % (pre, M, n)); save()
    step('errmap', [sys.executable, '-I', str(WK / 'TP_errmap.py'), str(OUT / 'lean-src' / (pre + 'Funs.lean')), str(OUT / 'summaries' / ('lean-%sFuns.log' % pre)), str(OUT / 'summaries' / 'errmap.json')], OUT / 'summaries' / 'errmap.txt')
    res['prefix'] = pre; res['finished'] = time.strftime('%Y-%m-%dT%H:%M:%SZ', time.gmtime()); save()
    note('DONE')

if __name__ == '__main__': main()
