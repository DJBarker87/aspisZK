#!/usr/bin/env python3
"""Aspis freeze emission driver. Runs INSIDE the fv_slot.sh scope of fv_frz_emit.sh (never directly).
usage: fv_frz_emit_run.py <source tree> <out dir> <config.json> <program features> <verifier features>
       fv_frz_emit_run.py rows-only <out dir>                 (rebuild rows.tsv from an existing run; reads only)
       fv_frz_emit_run.py rows-ref <json-out> <crate> <adapted Funs.lean> <adapted FunsExternal.lean> <Funs lean log> [<Funs exit>]
                                                              (the same row rule applied to another worker's emission)
Per scope of the config (order of config["order"]):
  1 Charon, second pair, the command line and environment of the workers' TP_charon.py / XP_charon.py
    (cargo --preset aeneas --mir built, --release --lib --locked --offline, nightly-2026-09-17, overflow checks as the
    scope says), source tree read only, one cargo target directory per tree and scope under frz-emit/target;
  2 Aeneas, second pair, WITH -abort-on-error (the release-style emission); only if it exits non-zero, once more
    without it to list every rejection (that run is then the one the rows use, and the scope is marked);
  3 scans: TP_llbc_scan.py for the scope's own crate (completeness by span, mutable-borrow type arguments under an
    erased region), TP_llbc_scan.py for the other crates in the LLBC (non-local functions with a body that were not
    emitted: the silent drop of the core note, section 4), tp3_erased_scan.py (the core worker's scan), a source
    search of the scope's crates for a reversed mutable iterator (iter_mut / chunks_mut / chunks_exact_mut ... .rev());
  4 Lean: the scope's adaptation tool and rules (the worker's), four modules compiled one at a time by
    fv_frz_emit_lean_one.sh against the L187 objects with the three shims, the error map of the workers (TP_errmap.py);
then the function text of the scope crates against the pin tree (TP_fntext.py) and the row table rows.tsv."""
import bisect, collections, hashlib, json, os, re, subprocess, sys, time
from pathlib import Path
B = Path(__file__).resolve().parent
WK = B / 'worker'
CHARON_DIR = '/home/dombarker/project-offloads/codex-pc-prov-p4x-20261110/PCWH_T004_out/bin'
CHARON_SHA = '57aa2359bb3e9a84480f7e4802dcdc700ef05709de30ec0eb97581b3f9c5f851'
DRIVER_SHA = '6a6552bce70d59e041fb96a67c08294377ef16d3f77a7876fea7f1250ee37845'
AENEAS = '/home/dombarker/project-offloads/codex-pc-prov-p4x-20261110/PCWH_T004_out/bin/aeneas'
AENEAS_SHA = '230ee9f0c4902ea3415a01960f6887e2d4c71bc82e8b4e78dfac398da657df91'
MODS = ('TypesExternal', 'Types', 'FunsExternal', 'Funs')
sha = lambda p: hashlib.sha256(Path(p).read_bytes()).hexdigest()

# ---------------------------------------------------------------- row rule (shared with rows-ref)
HDR = re.compile(r"/-- (?:Trait implementation: |Trait declaration: )?\[([^\]]*(?:\][^\]]*)*?)\](:? loop[^\n]*)?:?\n(?:\s+Source: '([^']*)', lines (\d+):\d+-(\d+):\d+)?")
KIND = re.compile(r'(?m)^(?:@\[[^\n]*\]\s*)*(?:noncomputable\s+)?(def|axiom|structure|inductive|instance|abbrev|opaque)\b\s*(\S*)')
def blocks(path):
    """doc-comment blocks of an emitted (or adapted) Lean file: rust name, loop flag, source file and line, kind,
    1-based first and last line in the file"""
    p = Path(path)
    if not p.exists(): return []
    L = p.read_text().split('\n'); starts = [i for i, l in enumerate(L) if l.startswith('/-- ')]; out = []
    for k, s in enumerate(starts):
        e = starts[k + 1] if k + 1 < len(starts) else len(L)
        b = '\n'.join(L[s:e]); m = HDR.match(b)
        if not m: continue
        body = re.sub(r'(?s)^/--.*?-/\n', '', b); kd = KIND.search(body)
        out.append(dict(rust=' '.join(m.group(1).split()), loop=bool(m.group(2)), file=m.group(3), beg=m.group(4), kind=kd.group(1) if kd else None,
                        sorry=bool(re.search(r'(?m)^\s*sorry\s*$', b)), first=s + 1, last=e))
    return out
def owner(r):
    m = re.search(r' for ([\w:]+?)::closure', r)
    if m: return m.group(1)
    r = re.sub(r'::\{(?:impl )?core::ops::function.*$', '', r)
    return re.sub(r'::closure.*$', '', r)
def is_row(r, crate):
    return r.split('::')[0] == crate and not re.search(r'\{impl core::|closure|core::ops::function', r)
def lean_errors(log, module_file):
    errs = []
    for m in re.finditer(r'(?m)^([^\n:]*\.lean):(\d+):(\d+): error(?:\([^)]*\))?: ([^\n]*)', log):
        if m.group(1).endswith('/' + module_file) or m.group(1) == module_file: errs.append((int(m.group(2)), ' '.join(m.group(4).split())[:200]))
    return errs
LIBRARY = re.compile(r'(?i)unknown (identifier|constant)|is not a field of|failed to synthesize|unknown namespace')
def make_rows(crate, funs_path, ext_path, funs_log, funs_exit, aeneas_errs=None, gaps=(), timeout=False):
    """one row per function of <crate> with a doc block in Funs or FunsExternal (closures, loop bodies, core-trait impl
    methods and type declarations are not rows; errors in loop bodies and closures count for their function)"""
    fb = blocks(funs_path); xb = blocks(ext_path)
    errs = lean_errors(funs_log or '', Path(funs_path).name)
    starts = [b['first'] for b in fb]
    by_block = collections.defaultdict(list)
    for ln, t in errs:
        k = bisect.bisect_right(starts, ln) - 1
        by_block[k if k >= 0 else -1].append(t)
    determined = funs_log is not None and (funs_exit == 0 or errs) and not timeout
    rows = collections.OrderedDict(); other_failing = []; pending = []
    def gap_of(r):
        for g in gaps:
            if re.search(g['match'], r): return g
        return None
    for src, bl in (('Funs', fb), ('FunsExternal', xb)):
        for k, b in enumerate(bl):
            r = b['rust']
            if b['kind'] in ('structure', 'inductive') : continue
            if not is_row(r, crate) or b['loop']:
                if src == 'Funs' and by_block.get(k): pending.append((r, b['loop'], by_block[k]))
                continue
            if b['kind'] == 'instance': continue
            key = (r, b['file'], b['beg'])
            row = rows.setdefault(key, dict(function=r, file=(b['file'] or ''), line=b['beg'], emitted=[], lean_errs=[], aeneas=[]))
            row['emitted'].append('axiom' if b['kind'] == 'axiom' else 'placeholder' if b['sorry'] else 'definition')
            if src == 'Funs' and by_block.get(k): row['lean_errs'].extend(by_block[k])
    for r, lp, es in pending:   # errors in loop bodies and closures count for the function that owns them
        o = r if lp else owner(r)
        tgt = [x for x in rows.values() if x['function'] == o]
        if tgt and r.split('::')[0] == crate:
            for x in tgt: x['lean_errs'].append(('loop: ' if lp else 'closure: ') + es[0])
        else: other_failing.append(dict(rust=r, errors=es[:2]))
    for r, e in (aeneas_errs or {}).items():
        if not is_row(r, crate): continue
        hit = [x for x in rows.values() if x['function'].replace(' ', '') == r.replace(' ', '')]
        if hit:
            for x in hit: x['aeneas'] = [y['kind'] + ': ' + y['error'] for y in e]
        else: rows[(r, '', None)] = dict(function=r, file='', line=None, emitted=['nothing'], lean_errs=[], aeneas=[y['kind'] + ': ' + y['error'] for y in e])
    out = []
    for row in rows.values():
        g = gap_of(row['function'])
        em = row['emitted']
        if 'definition' in em and not row['aeneas']:
            tr = 'yes'
            if not determined: el = 'not determined (%s)' % ('Funs timed out' if timeout else 'Funs did not compile and gave no error line' if funs_log is not None else 'Lean not run')
            elif row['lean_errs']: el = 'no: ' + row['lean_errs'][0]
            else: el = 'yes'
        elif 'axiom' in em and not row['aeneas']:
            tr = 'opaque in this emission' + (' (named gap)' if g else ' (opaque pattern of the scope)'); el = 'not run (opaque)'
        else:
            tr = 'no: ' + (row['aeneas'][0] if row['aeneas'] else 'placeholder emitted' if 'placeholder' in em else 'not emitted')[:200]; el = 'not run (not translated)'
        out.append(dict(function=row['function'], file=row['file'], line=row['line'], translates=tr, elaborates=el, gap=(g or {}).get('reason'),
                        library=bool(row['lean_errs']) and all(LIBRARY.search(x) for x in row['lean_errs'])))
    return out, other_failing
def aeneas_summary(logtext):
    log = re.sub(r'\x1b\[[0-9;]*m', '', logtext); res = {}; last = None
    for b in re.split(r'(?m)^(?=\[Error\])', log):
        if not b.startswith('[Error]'): continue
        msg = b.split('\n', 1)[0][len('[Error] '):].strip()
        src = re.search(r"(?m)^Source: '([^']*)', lines ([0-9:\-]+)", b)
        m = re.search(r"Could not translate the (?:body of function|function signature of|function) '(.*?) because of previous error", b, re.S) or re.search(r"Ignoring the body of '(.*?)' because of previous error", msg)
        where = ('%s %s' % (src.group(1).split('/src/')[-1], src.group(2))) if src else ''
        if m:
            fn = ' '.join(m.group(1).split()); kind = 'signature' if 'function signature' in b else 'body'
            if msg.startswith('Ignoring the body'):
                if last: res.setdefault(fn, []).append(dict(kind='body', error=last[0], at=last[1]))
            else: res.setdefault(fn, []).append(dict(kind=kind, error=msg, at=where))
            last = None
        else: last = (msg, where)
    return res

# ---------------------------------------------------------------- class from the function-text comparison
def classify(rows, fntext, src, pin, reshaped):
    by_line = collections.defaultdict(list)
    for k, v in fntext.items():
        f, key = k.split('|', 1); by_line[f].append((v.get('line_b'), key.split('::')[-1].split('#')[0], v['status']))
    for r in rows:
        bare = re.sub(r'<.*', '', r['function']).split('::')[-1]
        st = None
        if r['file'] and r['line']:
            ln = int(r['line']); cands = [x for x in by_line.get(r['file'], []) if x[0] is not None and x[1] == bare and ln - 2 <= x[0] <= ln + 12]
            if cands: st = min(cands, key=lambda x: abs(x[0] - ln))[2]
            elif (src / r['file']).exists():   # constants and statics: the item's first line, looked up in the pin file
                L = (src / r['file']).read_text().split('\n'); t = L[ln - 1].strip() if ln - 1 < len(L) else ''
                pf = pin / r['file']
                st = ('identical' if pf.exists() and t and t in [x.strip() for x in pf.read_text().split('\n')] else 'not present at A') if t else None
        r['pin'] = st or 'not compared'
        if r['gap']: c = 'named gap'
        elif r['translates'] == 'yes' and r['elaborates'].startswith('no') and r['library']: c = 'needs library models'
        elif st == 'identical': c = 'R1 text identical to the pin'
        elif st == 'identical under an added cfg attribute': c = 'identical under an added cfg'
        elif st in ('CHANGED', 'whitespace only'): c = 'reshaped in the pass' if any(re.search(x, r['function']) for x in reshaped) else 'Aspis-only new gate (changed against the pin)'
        elif st == 'not present at A': c = 'Aspis-only new gate'
        else: c = 'not compared'
        r['class'] = c
    return rows
def category(r):
    if r['class'] == 'named gap': return 'named gap'
    if r['translates'] == 'yes': return 'translates and elaborates' if r['elaborates'] == 'yes' else 'translates only'
    if r['translates'].startswith('opaque'): return 'opaque (not a named gap)'
    return 'does not translate'

# ---------------------------------------------------------------- the run
def main():
    SRC, OUT, CFG, PF, VF = Path(sys.argv[1]), Path(sys.argv[2]), Path(sys.argv[3]), sys.argv[4], sys.argv[5]
    cfg = json.loads(CFG.read_text()); F = OUT.parent
    for d in ('runs', 'lean-src', 'lean-out', 'summaries', 'flat'): (OUT / d).mkdir(parents=True, exist_ok=True)
    ST = OUT / 'steps.txt'
    def note(s):
        with open(ST, 'a') as f: f.write(s + '\n')
    def step(name, cmd, out_path, cwd=None, env=None):
        t0 = time.time()
        with open(out_path, 'w') as fo: rc = subprocess.run(cmd, stdout=fo, stderr=subprocess.STDOUT, cwd=cwd, env=env).returncode
        w = round(time.time() - t0, 1); note('%s exit %d; wall %s s' % (name, rc, w)); return rc, w
    assert sha(CHARON_DIR + '/charon') == CHARON_SHA and sha(CHARON_DIR + '/charon-driver') == DRIVER_SHA and sha(AENEAS) == AENEAS_SHA, 'tool hash mismatch'
    (OUT / 'config.json').write_text(CFG.read_text())
    res = dict(source=str(SRC), config_sha256=sha(CFG), program_features=PF, verifier_features=VF, charon_sha256=CHARON_SHA, charon_driver_sha256=DRIVER_SHA,
               aeneas_sha256=AENEAS_SHA, started=time.strftime('%Y-%m-%dT%H:%M:%SZ', time.gmtime()), tools={p.name: sha(p) for p in sorted(WK.iterdir()) if p.is_file()},
               bin={p.name: sha(p) for p in sorted(B.iterdir()) if p.is_file()}, scopes={})
    note('source %s; out %s; config sha256 %s' % (SRC, OUT, res['config_sha256']))
    # shims of copied library definitions (the workers'), compiled first into this run's own object directory
    for s in cfg['shims']:
        (OUT / 'lean-src' / (s + '.lean')).write_bytes((WK / (s + '.lean')).read_bytes())
        rc, w = step('lean-shim-' + s, ['bash', str(B / 'fv_frz_emit_lean_one.sh'), str(OUT), s], OUT / 'summaries' / ('lean-' + s + '.log'))
        res.setdefault('shims', {})[s] = dict(sha256=sha(OUT / 'lean-src' / (s + '.lean')), exit=rc, wall=w)
    for X in cfg['order']:
        sc = cfg['scopes'][X]; r = res['scopes'][X] = dict(crate=sc['crate'], scope=sc['scope'])
        feats = {'@program': PF, '@verifier': VF}.get(sc['features'], sc['features'])
        cdir = OUT / 'runs' / ('C-' + X); cdir.mkdir(); llbc = cdir / 'out.llbc'
        cmd = [CHARON_DIR + '/charon', 'cargo', '--preset', 'aeneas', '--mir', 'built', '--sysroot', 'default',
               '--include', 'core::option::Option', '--include', 'core::result::Result', '--include', 'core::option::_::ok_or']
        for x in sc['roots']: cmd += ['--start-from', x]
        for x in sc.get('opaque', []): cmd += ['--opaque', x]
        for x in sc.get('include', []): cmd += ['--include', x]
        for x in sc.get('exclude', []): cmd += ['--exclude', x]
        cmd += ['--dest-file', str(llbc), '--', '--manifest-path', str(SRC / sc['manifest']), '--locked', '--offline', '--release', '--lib', '--jobs', '4', '--features', feats]
        env = {k: v for k, v in os.environ.items() if k not in ('RUSTFLAGS', 'RUSTC_WRAPPER', 'RUSTC_WORKSPACE_WRAPPER', 'CARGO_ENCODED_RUSTFLAGS', 'CHARON_TOOLCHAIN_IS_IN_PATH')}
        env.update(PATH='/home/dombarker/.cargo/bin:/usr/bin:/bin', RUSTUP_TOOLCHAIN='nightly-2026-09-17', CARGO_TARGET_DIR=str(F / 'target' / (SRC.name + '-' + X)),
                   CARGO_NET_OFFLINE='true', CARGO_BUILD_JOBS='4', RAYON_NUM_THREADS='1', CARGO_PROFILE_RELEASE_CODEGEN_UNITS='2')
        if sc['overflow_checks']: env.update(RUSTFLAGS='-Zthreads=1 -C link-arg=-Wl,--threads=1 -C overflow-checks=yes', CARGO_PROFILE_RELEASE_OVERFLOW_CHECKS='true')
        else: env.update(RUSTFLAGS='-Zthreads=1 -C link-arg=-Wl,--threads=1')
        (cdir / 'charon_command.json').write_text(json.dumps(dict(command=cmd, env={k: env.get(k) for k in ('PATH', 'RUSTUP_TOOLCHAIN', 'CARGO_TARGET_DIR', 'CARGO_NET_OFFLINE', 'CARGO_BUILD_JOBS', 'RAYON_NUM_THREADS', 'CARGO_PROFILE_RELEASE_CODEGEN_UNITS', 'RUSTFLAGS', 'CARGO_PROFILE_RELEASE_OVERFLOW_CHECKS')}), indent=1) + '\n')
        lock0 = sha(SRC / 'Cargo.lock')
        rc, w = step('charon-' + X, ['/usr/bin/time', '-v', '-o', str(cdir / 'charon.time')] + cmd, cdir / 'charon.log', cwd=SRC, env=env)
        r['charon'] = dict(exit=rc, wall=w, lock_unchanged=sha(SRC / 'Cargo.lock') == lock0, peak_rss_kib=next((int(l.split(':')[1]) for l in (cdir / 'charon.time').read_text().splitlines() if 'Maximum resident' in l), None))
        if rc != 0 or not llbc.exists():
            note('   charon failed: ' + ' | '.join((cdir / 'charon.log').read_text(errors='replace').splitlines()[-4:])[:600]); continue
        r['charon']['llbc_sha256'] = sha(llbc)
        doc = json.loads(llbc.read_text()); tr = doc.get('translated', doc)
        r['charon']['fun_decls'] = len([f for f in tr.get('fun_decls', []) if f]); r['charon']['has_errors'] = doc.get('has_errors')
        note('   llbc sha256 %s; %d function declarations' % (r['charon']['llbc_sha256'], r['charon']['fun_decls']))
        del doc, tr
        ns = sc['ns']; used = None
        for mode in ('release', 'noabort'):
            adir = OUT / 'runs' / ('A-%s-%s' % (X, mode)); adir.mkdir()
            acmd = [AENEAS, '-diagnose-translation', '-sequential', '-no-progress-bar'] + (['-abort-on-error'] if mode == 'release' else []) + \
                   ['-backend', 'lean', '-namespace', ns, '-dest', str(adir / 'raw'), '-subdir', ns, '-split-files', str(llbc)]
            (adir / 'aeneas_command.json').write_text(json.dumps(dict(command=acmd, llbc_sha256=sha(llbc)), indent=1) + '\n')
            rc, w = step('aeneas-%s-%s' % (X, mode), ['/usr/bin/time', '-v', '-o', str(adir / 'aeneas.time')] + acmd, adir / 'aeneas.log', cwd=adir)
            errs = aeneas_summary((adir / 'aeneas.log').read_text(errors='replace'))
            outs = {str(p.relative_to(adir)): sha(p) for p in sorted((adir / 'raw').rglob('*')) if p.is_file()} if (adir / 'raw').exists() else {}
            r['aeneas_' + mode] = dict(exit=rc, wall=w, rejected_functions=len(errs), error_lines=(adir / 'aeneas.log').read_text(errors='replace').count('[Error]'),
                                      peak_rss_kib=next((int(l.split(':')[1]) for l in (adir / 'aeneas.time').read_text().splitlines() if 'Maximum resident' in l), None), outputs=outs)
            note('   aeneas %s: exit %d, functions with errors %d' % (mode, rc, len(errs)))
            used = (adir, errs, mode)
            if mode == 'release' and rc == 0: break
        adir, aerrs, mode = used; raw = adir / 'raw' / ns; r['emission_used'] = mode
        json.dump(aerrs, open(OUT / 'summaries' / ('aeneas-errors-%s.json' % X), 'w'), indent=1)
        if not (raw / 'Funs.lean').exists(): note('   no Funs.lean emitted'); continue
        # scans
        own = sc['crate'] + '::'; others = [c + '::' for c in sc['other_crates']]
        step('scan-' + X, [sys.executable, '-I', str(WK / 'TP_llbc_scan.py'), str(cdir), str(raw), str(OUT / 'summaries' / ('scan-%s.json' % X)), own], OUT / 'summaries' / ('scan-%s.txt' % X))
        if others: step('scan-nonlocal-' + X, [sys.executable, '-I', str(WK / 'TP_llbc_scan.py'), str(cdir), str(raw), str(OUT / 'summaries' / ('scan-nonlocal-%s.json' % X))] + others, OUT / 'summaries' / ('scan-nonlocal-%s.txt' % X))
        step('erased-' + X, [sys.executable, '-I', str(WK / 'tp3_erased_scan.py'), str(llbc), str(raw / 'Funs.lean'), sc['crate']], OUT / 'summaries' / ('erased-%s.json' % X))
        hits = []
        for d in sc['crate_dirs']:
            for p in sorted((SRC / d).rglob('*.rs')):
                t = p.read_text(errors='replace')
                for m in re.finditer(r'\b(iter_mut|chunks_mut|chunks_exact_mut|rchunks_mut|split_at_mut|values_mut)\s*\([^;{}]*?\)\s*(?:\.\s*\w+\s*\([^;{}]*?\)\s*)*\.\s*rev\s*\(\s*\)', t):
                    hits.append('%s:%d' % (p.relative_to(SRC), t.count('\n', 0, m.start()) + 1))
        r['reversed_mutable_iterator_sites'] = hits
        # Lean
        pre = 'AspisFRZ' + re.sub(r'\W', '', OUT.name) + X
        rc, _ = step('adapt-' + X, [sys.executable, '-I', str(WK / sc['adapt']), str(raw), ns, pre, str(OUT / 'flat' / pre), str(WK / sc['rules'])], OUT / 'summaries' / ('adapt-%s.json' % pre))
        r['lean'] = {}
        for p in sorted((OUT / 'flat' / pre).glob('*.lean')): (OUT / 'lean-src' / p.name).write_bytes(p.read_bytes())
        timeout = False
        for M in MODS:
            if not (OUT / 'lean-src' / (pre + M + '.lean')).exists(): r['lean'][M] = 'absent'; continue
            logp = OUT / 'summaries' / ('lean-%s%s.log' % (pre, M))
            rc, w = step('lean-%s%s' % (pre, M), ['bash', str(B / 'fv_frz_emit_lean_one.sh'), str(OUT), pre + M], logp)
            n = len(re.findall(r': error', logp.read_text(errors='replace')))
            r['lean'][M] = dict(exit=rc, wall=w, errors=n, sha256=sha(OUT / 'lean-src' / (pre + M + '.lean')))
            if M == 'Funs' and rc == 124: timeout = True
            note('   errors in %s%s: %d' % (pre, M, n))
        step('errmap-' + X, [sys.executable, '-I', str(WK / 'TP_errmap.py'), str(OUT / 'lean-src' / (pre + 'Funs.lean')), str(OUT / 'summaries' / ('lean-%sFuns.log' % pre)), str(OUT / 'summaries' / ('errmap-%s.json' % X))], OUT / 'summaries' / ('errmap-%s.txt' % X))
        r['prefix'] = pre; r['funs_timeout'] = timeout
        json.dump(res, open(OUT / 'result.json', 'w'), indent=1)
    # function text against the pin
    pin = Path(cfg['pin_dir']) if cfg['pin_dir'].startswith('/') else F / cfg['pin_dir']
    files = set()
    for X in cfg['order']:
        for d in cfg['scopes'][X]['crate_dirs']:
            for root in (SRC, pin):
                files |= {str(p.relative_to(root)) for p in (root / d).rglob('*.rs')} if (root / d).exists() else set()
    step('fntext', [sys.executable, '-I', str(WK / 'TP_fntext.py'), 'dir:' + str(pin), 'dir:' + str(SRC), str(OUT / 'summaries' / 'fntext.json')] + sorted(files), OUT / 'summaries' / 'fntext.txt')
    json.dump(res, open(OUT / 'result.json', 'w'), indent=1)
    rows_only(OUT, SRC, pin)
    res['finished'] = time.strftime('%Y-%m-%dT%H:%M:%SZ', time.gmtime()); json.dump(res, open(OUT / 'result.json', 'w'), indent=1)
    note('DONE')

def rows_only(OUT, SRC=None, pin=None):
    cfg = json.loads((OUT / 'config.json').read_text()); res = json.loads((OUT / 'result.json').read_text())
    SRC = SRC or Path(res['source']); F = OUT.parent
    pin = pin or (Path(cfg['pin_dir']) if cfg['pin_dir'].startswith('/') else F / cfg['pin_dir'])
    fntext = json.loads((OUT / 'summaries' / 'fntext.json').read_text()) if (OUT / 'summaries' / 'fntext.json').exists() else {}
    allrows = []; counts = {}; checks = {}
    for X in cfg['order']:
        sc = cfg['scopes'][X]; r = res['scopes'].get(X, {}); pre = r.get('prefix')
        if not pre: continue
        logp = OUT / 'summaries' / ('lean-%sFuns.log' % pre)
        lean = r.get('lean', {}).get('Funs')
        aerrs = json.loads((OUT / 'summaries' / ('aeneas-errors-%s.json' % X)).read_text())
        gaps = [g for g in cfg.get('named_gaps', []) if g['scope'] == X]
        rows, other = make_rows(sc['crate'], OUT / 'lean-src' / (pre + 'Funs.lean'), OUT / 'lean-src' / (pre + 'FunsExternal.lean'),
                                logp.read_text(errors='replace') if logp.exists() else None, lean['exit'] if isinstance(lean, dict) else None, aerrs, gaps, r.get('funs_timeout'))
        have = {x['function'] for x in rows}
        for g in gaps:   # named gaps the emission does not contain at all (excluded, or reached only through opaque items)
            if g.get('row') and not any(re.search(g['match'], f) for f in have):
                rows.append(dict(function=g['row'], file=g.get('file', ''), line=g.get('line'), translates='not in this emission (%s)' % g.get('absent', 'excluded'), elaborates='not run', gap=g['reason'], library=False))
        for x in rows:   # the workers' adaptation rule 3 also rewrites module names inside the doc comments' Source paths
            m = re.search(r'(?:^|/)_root_\.\w+\.(\w+)\.rs$', x['file'] or '')
            if m:
                c = [str(q.relative_to(SRC)) for d in sc['crate_dirs'] for q in (SRC / d).rglob(m.group(1) + '.rs')]
                if len(c) == 1: x['file'] = c[0]
        classify(rows, fntext, SRC, pin, cfg.get('reshaped', {}).get(X, []))
        for x in rows: x['scope'] = sc['scope']; x['run'] = X; x['category'] = category(x)
        allrows += rows
        sc_scan = json.loads((OUT / 'summaries' / ('scan-%s.json' % X)).read_text()) if (OUT / 'summaries' / ('scan-%s.json' % X)).exists() else {}
        nl = json.loads((OUT / 'summaries' / ('scan-nonlocal-%s.json' % X)).read_text()) if (OUT / 'summaries' / ('scan-nonlocal-%s.json' % X)).exists() else {}
        er = json.loads((OUT / 'summaries' / ('erased-%s.json' % X)).read_text()) if (OUT / 'summaries' / ('erased-%s.json' % X)).exists() else {}
        log = logp.read_text(errors='replace') if logp.exists() else ''
        def derived(n): return bool(re.search(r'\{impl core::(clone::Clone|cmp::PartialEq|cmp::Eq|marker::|fmt::Debug|default::Default)|drop_in_place|\{drop|\{impl\}::(clone|eq)$|\{Builtin\}$', n))
        ne = sc_scan.get('not_emitted', [])
        checks[X] = dict(
            functions_with_body=sc_scan.get('functions_with_body'),
            local_not_emitted=len(ne), local_not_emitted_derived_or_drop=sum(1 for m in ne if derived(m['function']) or m['status'] != 'NOT EMITTED'),
            local_not_emitted_other=[m for m in ne if not derived(m['function']) and m['status'] == 'NOT EMITTED'],
            local_not_emitted_list=['%s | %s:%s | %s' % (m['function'], m['file'].split('/src/')[-1], m['line'], m['status']) for m in ne],
            nonlocal_with_body=nl.get('functions_with_body'), nonlocal_not_emitted=['%s | %s:%s | %s' % (m['function'], (m['file'] or '').split('/src/')[-1], m['line'], m['status']) for m in nl.get('not_emitted', [])],
            mut_borrow_type_args_erased_TP=len(sc_scan.get('mutable_borrow_type_arguments_with_erased_region', {})),
            mut_borrow_type_args_erased_tp3=len(er.get('erased_mut_type_args', [])), tp3_missing_from_emission=len(er.get('missing_from_emission', [])),
            tp3_missing_list=[m['source'] + ' ' + ','.join(m['names']) for m in er.get('missing_from_emission', [])],
            lean_unknown_identifier_errors=len(re.findall(r'(?i)unknown (identifier|constant)', log)),
            sorry_in_funs=len(re.findall(r'(?m)^\s*sorry\s*$', (OUT / 'lean-src' / (pre + 'Funs.lean')).read_text())) if (OUT / 'lean-src' / (pre + 'Funs.lean')).exists() else None,
            reversed_mutable_iterator_sites=r.get('reversed_mutable_iterator_sites'), other_failing_declarations=other)
    cols = ('scope', 'run', 'function', 'file_line', 'translates', 'elaborates', 'class', 'pin_text', 'note')
    with open(OUT / 'rows.tsv', 'w') as f:
        f.write('\t'.join(cols) + '\n')
        for x in allrows:
            f.write('\t'.join(str(v).replace('\t', ' ') for v in (x['scope'], x['run'], x['function'], '%s:%s' % (x['file'].split('/src/')[-1] if x['file'] else '', x['line'] or ''),
                                                                 x['translates'], x['elaborates'], x['class'], x['pin'], x.get('gap') or '')) + '\n')
    tot = collections.defaultdict(collections.Counter)
    seen = set()
    for x in allrows:
        k = (x['scope'], x['function'], x['file'], x['line'])
        if k in seen: tot[x['scope']]['duplicate across runs (counted once)'] += 1; continue
        seen.add(k); tot[x['scope']]['rows'] += 1; tot[x['scope']][x['category']] += 1; tot['overall']['rows'] += 1; tot['overall'][x['category']] += 1
    json.dump(dict(totals={k: dict(v) for k, v in tot.items()}, checks=checks), open(OUT / 'totals.json', 'w'), indent=1)
    print(json.dumps({k: dict(v) for k, v in tot.items()}, indent=1))

if __name__ == '__main__':
    if sys.argv[1] == 'rows-only': rows_only(Path(sys.argv[2]))
    elif sys.argv[1] == 'rows-ref':
        outj, crate, funs, ext, logp = sys.argv[2:7]; ex = int(sys.argv[7]) if len(sys.argv) > 7 else None
        rows, other = make_rows(crate, funs, ext, Path(logp).read_text(errors='replace'), ex)
        json.dump(dict(rows=rows, other_failing=other), open(outj, 'w'), indent=1)
        print(json.dumps(collections.Counter((x['translates'][:20], x['elaborates'][:12]) for x in rows).most_common()))
    else: main()
