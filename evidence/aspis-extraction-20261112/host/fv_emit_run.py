#!/usr/bin/env python3
"""X7: one Charon run and one Aeneas run (-abort-on-error) of one on-chain program of a source tree. Runs INSIDE the
fv_slot.sh scope of fv_emit_job.sh, never directly. A tool record; nothing here is a proof.

usage: fv_emit_run.py <program config.json> <tree dir> <out dir> <cargo target dir>

The command line and environment are those of the workers' runners, taken from the config:
  verifier program: X1/X1b's fv_x1_run.py (flag order: Option/Result includes, roots, include, opaque, exclude;
                    CARGO_PROFILE_RELEASE_OVERFLOW_CHECKS=false set explicitly; the two deployment ids in the env)
  Pool:             X2's fv_x2_run.py (flag order: Option/Result includes, roots, opaque, include, exclude, extra;
                    CARGO_PROFILE_RELEASE_OVERFLOW_CHECKS removed from the environment, the release default `false`)
Charon: --preset aeneas --mir built --sysroot default, cargo --locked --offline --release --lib --jobs 4, toolchain
nightly-2026-09-17. Aeneas: -diagnose-translation -sequential -no-progress-bar -abort-on-error <extra> -backend lean
-namespace <ns> -dest <out>/aeneas/raw -subdir <ns> -split-files <llbc>.
Writes <out>/charon/{out.llbc,charon.log,charon.time,charon_command.json}, <out>/aeneas/{raw/,aeneas.log,aeneas.time,
aeneas_command.json}, <out>/result.json. Exit: 0 iff the tool hashes match, Charon exits 0 and Aeneas exits 0."""
import hashlib, json, os, subprocess, sys, time
from pathlib import Path

CHARON_DIR = '/home/dombarker/project-offloads/codex-pc-prov-p4x-20261110/PCWH_T004_out/bin'
TOOLS = {'charon': (CHARON_DIR + '/charon', '57aa2359bb3e9a84480f7e4802dcdc700ef05709de30ec0eb97581b3f9c5f851'),
         'charon-driver': (CHARON_DIR + '/charon-driver', '6a6552bce70d59e041fb96a67c08294377ef16d3f77a7876fea7f1250ee37845'),
         'aeneas': (CHARON_DIR + '/aeneas', '230ee9f0c4902ea3415a01960f6887e2d4c71bc82e8b4e78dfac398da657df91')}
sha = lambda p: hashlib.sha256(Path(p).read_bytes()).hexdigest()


def peak(tf):
    try:
        t = Path(tf).read_text().splitlines()
        return (next((int(l.split(':')[1]) for l in t if 'Maximum resident' in l), None),
                next((l.split(': ', 1)[1].strip() for l in t if 'Elapsed (wall' in l), None))
    except FileNotFoundError:
        return None, None


def main():
    cfg = json.loads(Path(sys.argv[1]).read_text())
    SRC, OUT, TGT = Path(sys.argv[2]), Path(sys.argv[3]), sys.argv[4]
    (OUT / 'charon').mkdir(parents=True, exist_ok=True)
    (OUT / 'aeneas').mkdir(parents=True, exist_ok=True)
    res = dict(program=cfg['program'], config=cfg, source=str(SRC), started=time.strftime('%Y-%m-%dT%H:%M:%SZ', time.gmtime()))
    save = lambda: (OUT / 'result.json').write_text(json.dumps(res, indent=1) + '\n')
    res['tools'] = {k: dict(path=p, sha256=sha(p), expected=e) for k, (p, e) in TOOLS.items()}
    if any(v['sha256'] != v['expected'] for v in res['tools'].values()):
        res['tool_hash_check'] = 'FAIL'
        save()
        print('tool hash mismatch')
        return 3
    res['tool_hash_check'] = 'pass'
    llbc = OUT / 'charon' / 'out.llbc'
    cmd = [TOOLS['charon'][0], 'cargo', '--preset', 'aeneas', '--mir', 'built', '--sysroot', 'default',
           '--include', 'core::option::Option', '--include', 'core::result::Result', '--include', 'core::option::_::ok_or']
    for part in cfg['flag_order']:
        if part == 'roots':
            for x in cfg['roots']: cmd += ['--start-from', x]
        elif part == 'extra':
            cmd += cfg.get('charon_extra', [])
        else:
            for x in cfg.get(part, []): cmd += ['--' + part, x]
    cmd += ['--dest-file', str(llbc), '--', '--manifest-path', str(SRC / cfg['manifest']), '--locked', '--offline',
            '--release', '--lib', '--jobs', '4', '--features', cfg['features']]
    drop = ('RUSTFLAGS', 'RUSTC_WRAPPER', 'RUSTC_WORKSPACE_WRAPPER', 'CARGO_ENCODED_RUSTFLAGS', 'CHARON_TOOLCHAIN_IS_IN_PATH',
            'CARGO_PROFILE_RELEASE_OVERFLOW_CHECKS', 'ASPIS_R1_POOL_PROGRAM_ID', 'ASPIS_R1_REGISTRY_PROGRAM_ID')
    env = {k: v for k, v in os.environ.items() if k not in drop}
    env.update(PATH='/home/dombarker/.cargo/bin:/usr/bin:/bin', RUSTUP_TOOLCHAIN='nightly-2026-09-17', CARGO_TARGET_DIR=TGT,
               CARGO_NET_OFFLINE='true', CARGO_BUILD_JOBS='4', RAYON_NUM_THREADS='1', CARGO_PROFILE_RELEASE_CODEGEN_UNITS='2',
               RUSTFLAGS='-Zthreads=1 -C link-arg=-Wl,--threads=1')
    assert cfg['overflow_checks'] is False, 'the pin is declared with overflow checks off'
    if cfg['overflow_env_explicit']:
        env['CARGO_PROFILE_RELEASE_OVERFLOW_CHECKS'] = 'false'
    env.update(cfg.get('extra_env', {}))
    keys = ('PATH', 'RUSTUP_TOOLCHAIN', 'CARGO_TARGET_DIR', 'CARGO_NET_OFFLINE', 'CARGO_BUILD_JOBS', 'RAYON_NUM_THREADS',
            'CARGO_PROFILE_RELEASE_CODEGEN_UNITS', 'RUSTFLAGS', 'CARGO_PROFILE_RELEASE_OVERFLOW_CHECKS') + tuple(cfg.get('extra_env', {}))
    (OUT / 'charon' / 'charon_command.json').write_text(json.dumps(dict(command=cmd, env={k: env.get(k) for k in keys}, cwd=str(SRC)), indent=1) + '\n')
    lock0 = sha(SRC / 'Cargo.lock')
    t0 = time.time()
    with open(OUT / 'charon' / 'charon.log', 'w') as fo:
        rc = subprocess.run(['/usr/bin/time', '-v', '-o', str(OUT / 'charon' / 'charon.time')] + cmd, stdout=fo,
                            stderr=subprocess.STDOUT, cwd=SRC, env=env).returncode
    pk, wall = peak(OUT / 'charon' / 'charon.time')
    res['charon'] = dict(exit=rc, wall_s=round(time.time() - t0, 1), wall=wall, peak_rss_kib=pk, lock_unchanged=sha(SRC / 'Cargo.lock') == lock0)
    save()
    if rc != 0 or not llbc.exists():
        print('charon exit %d' % rc)
        return 4
    res['charon']['llbc_sha256'] = sha(llbc)
    doc = json.loads(llbc.read_text())
    tr = doc.get('translated', doc)
    res['charon']['fun_decls'] = len([f for f in tr.get('fun_decls', []) if f])
    res['charon']['has_errors'] = doc.get('has_errors')
    del doc, tr
    save()
    ns = cfg['ns']
    adir = OUT / 'aeneas'
    acmd = [TOOLS['aeneas'][0], '-diagnose-translation', '-sequential', '-no-progress-bar', '-abort-on-error'] + \
        cfg.get('aeneas_extra', []) + ['-backend', 'lean', '-namespace', ns, '-dest', str(adir / 'raw'), '-subdir', ns, '-split-files', str(llbc)]
    (adir / 'aeneas_command.json').write_text(json.dumps(dict(command=acmd, llbc_sha256=sha(llbc)), indent=1) + '\n')
    t0 = time.time()
    with open(adir / 'aeneas.log', 'w') as fo:
        rc = subprocess.run(['/usr/bin/time', '-v', '-o', str(adir / 'aeneas.time')] + acmd, stdout=fo, stderr=subprocess.STDOUT, cwd=adir).returncode
    pk, wall = peak(adir / 'aeneas.time')
    log = (adir / 'aeneas.log').read_text(errors='replace')
    outs = {str(p.relative_to(adir / 'raw')): sha(p) for p in sorted((adir / 'raw').rglob('*')) if p.is_file()} if (adir / 'raw').exists() else {}
    res['aeneas'] = dict(exit=rc, wall_s=round(time.time() - t0, 1), wall=wall, peak_rss_kib=pk, error_lines=log.count('[Error]'), outputs=outs)
    res['finished'] = time.strftime('%Y-%m-%dT%H:%M:%SZ', time.gmtime())
    save()
    print('charon exit 0; aeneas exit %d' % rc)
    return 0 if rc == 0 else 5


if __name__ == '__main__':
    sys.exit(main())
