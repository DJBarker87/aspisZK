#!/usr/bin/env python3
"""X2: first release-style translator emission of the Aspis Pool program (programs/aspis-pool) on the frozen tree.
Runs INSIDE one fv_slot.sh scope (started by fv_x2.sh; never directly). A tool record: which functions the second
tool pair (Charon 454586e9, Aeneas 0d21a9ec) translates and whether the emitted Lean elaborates against the R1 (L187)
library. Nothing here is a proof.
usage: fv_x2_run.py <config.json> <out dir> <stage>[,<stage>...]
stages (each appends to <out>/steps.txt and updates <out>/result.json):
  charon    Charon, the command line and environment of fv_frz_emit_run.py (--preset aeneas --mir built, --release
            --lib --locked --offline, nightly-2026-09-17), roots/opaque/include/exclude from the config, the deployed
            feature list, the config's overflow-check setting; source tree read only; cargo target directory from the
            config (under W/x2/target)
  aeneas    Aeneas with -abort-on-error (release)        -> <out>/runs/A-release
  noabort   Aeneas without -abort-on-error (exploratory)  -> <out>/runs/A-noabort
  scan      on the emission named by the config's "emission" (release or noabort): TP_llbc_scan.py for the Pool crate
            and for the two library crates, tp3_erased_scan.py, the reversed-mutable-iterator source search over the
            three crates' sources
  lean      adaptation (TP_adapt.py with the config's rules file) and the four modules compiled one at a time by
            fv_x2_lean_one.sh against the L187 objects, shims first
The config names every root, opaque item, include, the feature list and the overflow setting; this script names none."""
import hashlib, json, os, re, subprocess, sys, time
from pathlib import Path
B = Path(__file__).resolve().parent
WK = B / 'worker'
CHARON_DIR = '/home/dombarker/project-offloads/codex-pc-prov-p4x-20261110/PCWH_T004_out/bin'
CHARON_SHA = '57aa2359bb3e9a84480f7e4802dcdc700ef05709de30ec0eb97581b3f9c5f851'
DRIVER_SHA = '6a6552bce70d59e041fb96a67c08294377ef16d3f77a7876fea7f1250ee37845'
AENEAS = CHARON_DIR + '/aeneas'
AENEAS_SHA = '230ee9f0c4902ea3415a01960f6887e2d4c71bc82e8b4e78dfac398da657df91'
MODS = ('TypesExternal', 'Types', 'FunsExternal', 'Funs')
sha = lambda p: hashlib.sha256(Path(p).read_bytes()).hexdigest()
sys.path.insert(0, str(B / 'frz'))
import fv_frz_emit_run as FRZ   # the freeze emission's row rule and Aeneas log reader, copied unchanged (hash in result.json)

def peak(tf):
    try: return next((int(l.split(':')[1]) for l in Path(tf).read_text().splitlines() if 'Maximum resident' in l), None)
    except FileNotFoundError: return None

def main():
    CFG, OUT, stages = Path(sys.argv[1]), Path(sys.argv[2]), sys.argv[3].split(',')
    cfg = json.loads(CFG.read_text()); SRC = Path(cfg['source'])
    OUT.mkdir(parents=True, exist_ok=True)
    for d in ('runs', 'lean-src', 'lean-out', 'summaries', 'flat'): (OUT / d).mkdir(exist_ok=True)
    ST = OUT / 'steps.txt'
    def note(s):
        with open(ST, 'a') as f: f.write(s + '\n')
    def step(name, cmd, out_path, cwd=None, env=None):
        t0 = time.time()
        with open(out_path, 'w') as fo: rc = subprocess.run(cmd, stdout=fo, stderr=subprocess.STDOUT, cwd=cwd, env=env).returncode
        w = round(time.time() - t0, 1); note('%s %s exit %d; wall %s s' % (time.strftime('%H:%M:%S'), name, rc, w)); return rc, w
    assert sha(CHARON_DIR + '/charon') == CHARON_SHA and sha(CHARON_DIR + '/charon-driver') == DRIVER_SHA and sha(AENEAS) == AENEAS_SHA, 'tool hash mismatch'
    RJ = OUT / 'result.json'
    res = json.loads(RJ.read_text()) if RJ.exists() else {}
    res.setdefault('runs', []).append(dict(stages=stages, config=str(CFG), config_sha256=sha(CFG), started=time.strftime('%Y-%m-%dT%H:%M:%SZ', time.gmtime()),
               bin={p.name: sha(p) for p in sorted(B.iterdir()) if p.is_file()}, worker={p.name: sha(p) for p in sorted(WK.iterdir()) if p.is_file()},
               frz={p.name: sha(p) for p in sorted((B / 'frz').iterdir()) if p.is_file()}))
    res.update(source=str(SRC), charon_sha256=CHARON_SHA, charon_driver_sha256=DRIVER_SHA, aeneas_sha256=AENEAS_SHA)
    (OUT / ('config-%s.json' % time.strftime('%H%M%S'))).write_text(CFG.read_text())
    save = lambda: json.dump(res, open(RJ, 'w'), indent=1)
    note('== %s stages %s; config %s sha256 %s' % (time.strftime('%Y-%m-%dT%H:%M:%SZ', time.gmtime()), ','.join(stages), CFG, sha(CFG)))
    cdir = OUT / 'runs' / 'C'; llbc = cdir / 'out.llbc'; ns = cfg['ns']
    if cfg.get('llbc_from'):   # an Aeneas-only exploratory run on the LLBC of another run (read only)
        cdir = Path(cfg['llbc_from']); llbc = cdir / 'out.llbc'; assert 'charon' not in stages
    if 'charon' in stages:
        cdir.mkdir(exist_ok=True)
        cmd = [CHARON_DIR + '/charon', 'cargo', '--preset', 'aeneas', '--mir', 'built', '--sysroot', 'default',
               '--include', 'core::option::Option', '--include', 'core::result::Result', '--include', 'core::option::_::ok_or']
        for x in cfg['roots']: cmd += ['--start-from', x]
        for x in cfg.get('opaque', []): cmd += ['--opaque', x]
        for x in cfg.get('include', []): cmd += ['--include', x]
        for x in cfg.get('exclude', []): cmd += ['--exclude', x]
        cmd += cfg.get('charon_extra', [])
        cmd += ['--dest-file', str(llbc), '--', '--manifest-path', str(SRC / cfg['manifest']), '--locked', '--offline', '--release', '--lib', '--jobs', '4', '--features', cfg['features']]
        env = {k: v for k, v in os.environ.items() if k not in ('RUSTFLAGS', 'RUSTC_WRAPPER', 'RUSTC_WORKSPACE_WRAPPER', 'CARGO_ENCODED_RUSTFLAGS', 'CHARON_TOOLCHAIN_IS_IN_PATH', 'CARGO_PROFILE_RELEASE_OVERFLOW_CHECKS')}
        env.update(PATH='/home/dombarker/.cargo/bin:/usr/bin:/bin', RUSTUP_TOOLCHAIN='nightly-2026-09-17', CARGO_TARGET_DIR=cfg['target_dir'],
                   CARGO_NET_OFFLINE='true', CARGO_BUILD_JOBS='4', RAYON_NUM_THREADS='1', CARGO_PROFILE_RELEASE_CODEGEN_UNITS='2')
        if cfg['overflow_checks']: env.update(RUSTFLAGS='-Zthreads=1 -C link-arg=-Wl,--threads=1 -C overflow-checks=yes', CARGO_PROFILE_RELEASE_OVERFLOW_CHECKS='true')
        else: env.update(RUSTFLAGS='-Zthreads=1 -C link-arg=-Wl,--threads=1')
        keys = ('PATH', 'RUSTUP_TOOLCHAIN', 'CARGO_TARGET_DIR', 'CARGO_NET_OFFLINE', 'CARGO_BUILD_JOBS', 'RAYON_NUM_THREADS', 'CARGO_PROFILE_RELEASE_CODEGEN_UNITS', 'RUSTFLAGS', 'CARGO_PROFILE_RELEASE_OVERFLOW_CHECKS')
        (cdir / 'charon_command.json').write_text(json.dumps(dict(command=cmd, env={k: env.get(k) for k in keys}, cwd=str(SRC)), indent=1) + '\n')
        lock0 = sha(SRC / 'Cargo.lock')
        rc, w = step('charon', ['/usr/bin/time', '-v', '-o', str(cdir / 'charon.time')] + cmd, cdir / 'charon.log', cwd=SRC, env=env)
        r = res['charon'] = dict(exit=rc, wall=w, lock_unchanged=sha(SRC / 'Cargo.lock') == lock0, peak_rss_kib=peak(cdir / 'charon.time'))
        if llbc.exists():
            r['llbc_sha256'] = sha(llbc)
            doc = json.loads(llbc.read_text()); tr = doc.get('translated', doc)
            r['fun_decls'] = len([f for f in tr.get('fun_decls', []) if f]); r['has_errors'] = doc.get('has_errors')
            note('   llbc sha256 %s; %d function declarations; has_errors %s' % (r['llbc_sha256'], r['fun_decls'], r['has_errors']))
            del doc, tr
        else: note('   no llbc: ' + ' | '.join((cdir / 'charon.log').read_text(errors='replace').splitlines()[-6:])[:900])
        save()
    for mode in ('aeneas', 'noabort'):
        if mode not in stages: continue
        m = 'release' if mode == 'aeneas' else 'noabort'
        adir = OUT / 'runs' / ('A-' + m); adir.mkdir(exist_ok=True)
        acmd = [AENEAS, '-diagnose-translation', '-sequential', '-no-progress-bar'] + (['-abort-on-error'] if m == 'release' else []) + \
               cfg.get('aeneas_extra', []) + ['-backend', 'lean', '-namespace', ns, '-dest', str(adir / 'raw'), '-subdir', ns, '-split-files', str(llbc)]
        (adir / 'aeneas_command.json').write_text(json.dumps(dict(command=acmd, llbc_sha256=sha(llbc)), indent=1) + '\n')
        rc, w = step('aeneas-' + m, ['/usr/bin/time', '-v', '-o', str(adir / 'aeneas.time')] + acmd, adir / 'aeneas.log', cwd=adir)
        log = (adir / 'aeneas.log').read_text(errors='replace'); errs = FRZ.aeneas_summary(log)
        json.dump(errs, open(OUT / 'summaries' / ('aeneas-errors-%s.json' % m), 'w'), indent=1)
        outs = {str(p.relative_to(adir)): sha(p) for p in sorted((adir / 'raw').rglob('*')) if p.is_file()} if (adir / 'raw').exists() else {}
        res['aeneas_' + m] = dict(exit=rc, wall=w, rejected_functions=len(errs), error_lines=log.count('[Error]'), peak_rss_kib=peak(adir / 'aeneas.time'), outputs=outs, llbc_sha256=sha(llbc))
        note('   aeneas %s: exit %d, functions with errors %d, [Error] lines %d' % (m, rc, len(errs), log.count('[Error]')))
        save()
    em = cfg.get('emission', 'release'); adir = OUT / 'runs' / ('A-' + em); raw = adir / 'raw' / ns
    if 'scan' in stages:
        own = cfg['crate'] + '::'
        step('scan-own', [sys.executable, '-I', str(WK / 'TP_llbc_scan.py'), str(cdir), str(raw), str(OUT / 'summaries' / 'scan-own.json'), own], OUT / 'summaries' / 'scan-own.txt')
        for c in cfg['lib_crates']:   # completeness per crate (the lead's addition: Aeneas can drop non-local groups silently)
            step('scan-' + c, [sys.executable, '-I', str(WK / 'TP_llbc_scan.py'), str(cdir), str(raw), str(OUT / 'summaries' / ('scan-%s.json' % c)), c + '::'], OUT / 'summaries' / ('scan-%s.txt' % c))
        for c in [cfg['crate']] + cfg['lib_crates']:
            step('erased-' + c, [sys.executable, '-I', str(WK / 'tp3_erased_scan.py'), str(llbc), str(raw / 'Funs.lean'), c], OUT / 'summaries' / ('erased-%s.json' % c))
        hits = []
        for d in cfg['crate_dirs']:
            for p in sorted((SRC / d).rglob('*.rs')):
                t = p.read_text(errors='replace')
                for mm in re.finditer(r'\b(iter_mut|chunks_mut|chunks_exact_mut|rchunks_mut|rchunks_exact_mut|split_at_mut|values_mut|as_mut_slice)\s*\([^;{}]*?\)\s*(?:\.\s*\w+\s*\([^;{}]*?\)\s*)*\.\s*rev\s*\(\s*\)', t):
                    hits.append('%s:%d' % (p.relative_to(SRC), t.count('\n', 0, mm.start()) + 1))
                for mm in re.finditer(r'\.\s*rev\s*\(\s*\)', t):   # every .rev() in the sources, for a manual review of the mutable ones
                    pass
        res['reversed_mutable_iterator_sites'] = hits; note('   reversed mutable iterator sites: %s' % hits); save()
    if 'lean' in stages:
        pre = cfg['lean_prefix']
        for s in cfg['shims']:
            (OUT / 'lean-src' / (s + '.lean')).write_bytes((WK / (s + '.lean')).read_bytes())
            rc, w = step('lean-shim-' + s, ['bash', str(B / 'fv_x2_lean_one.sh'), str(OUT), s, str(cfg.get('lean_timeout', 180))], OUT / 'summaries' / ('lean-' + s + '.log'))
            res.setdefault('shims', {})[s] = dict(sha256=sha(OUT / 'lean-src' / (s + '.lean')), exit=rc, wall=w)
        rc, _ = step('adapt', [sys.executable, '-I', str(WK / cfg['adapt']), str(raw), ns, pre, str(OUT / 'flat' / pre), str(B / cfg['rules'])], OUT / 'summaries' / ('adapt-%s.json' % pre))
        for p in sorted((OUT / 'flat' / pre).glob('*.lean')): (OUT / 'lean-src' / p.name).write_bytes(p.read_bytes())
        res['lean'] = {}; res['lean_prefix'] = pre; res['emission_used'] = em
        for M in cfg.get('lean_modules', MODS):
            if not (OUT / 'lean-src' / (pre + M + '.lean')).exists(): res['lean'][M] = 'absent'; continue
            logp = OUT / 'summaries' / ('lean-%s%s.log' % (pre, M))
            t0 = time.time()
            rc, w = step('lean-%s%s' % (pre, M), ['/usr/bin/time', '-v', '-o', str(OUT / 'summaries' / ('lean-%s%s.time' % (pre, M))), 'bash', str(B / 'fv_x2_lean_one.sh'), str(OUT), pre + M, str(cfg.get('lean_timeout', 180))], logp)
            n = len(re.findall(r': error', logp.read_text(errors='replace')))
            res['lean'][M] = dict(exit=rc, wall=w, errors=n, sha256=sha(OUT / 'lean-src' / (pre + M + '.lean')), peak_rss_kib=peak(OUT / 'summaries' / ('lean-%s%s.time' % (pre, M))))
            note('   errors in %s%s: %d' % (pre, M, n)); save()
            if rc != 0 and M != 'Funs' and cfg.get('stop_on_module_error', True): note('   stop: %s failed' % M); break
    res['runs'][-1]['finished'] = time.strftime('%Y-%m-%dT%H:%M:%SZ', time.gmtime()); save()
    note('DONE')

if __name__ == '__main__': main()
