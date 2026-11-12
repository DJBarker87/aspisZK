#!/usr/bin/env python3
"""X7: MANIFEST.json of one candidate run, from the run directory only (reads; writes <run>/MANIFEST.json).
Source commit and tree hashes (the files fv_frz_tree.sh wrote into the tree), tool and library hashes, every flag
(the exact Charon and Aeneas command lines and environments as run), the resolved feature sets of each Aspis crate in
each build (host and SBF), the overflow setting, sha256 of each LLBC and of each raw Lean file, the Lean version and
the library's package revisions, the opaque lists, the compile-time constants, the step table, the gate lines, the
native-compile results and the sha256 of every script in the driver's directory.
usage: fv_emit_manifest.py <tree> <run dir> <verifier config.json> <pool config.json>"""
import hashlib, json, re, sys, time
from pathlib import Path
sys.path.insert(0, str(Path(__file__).resolve().parent))
import fv_emit_cfg as C

tree, run = Path(sys.argv[1]), Path(sys.argv[2])
B = Path(__file__).resolve().parent
LIB = Path('/home/dombarker/project-offloads/future-version-20261111/x3/aeneas-src/backends/lean')
sha = lambda p: hashlib.sha256(Path(p).read_bytes()).hexdigest()
rd = lambda p: Path(p).read_text().strip() if Path(p).exists() else None
m = dict(generated=time.strftime('%Y-%m-%dT%H:%M:%SZ', time.gmtime()), status='tool record; nothing here is a proof')
m['source'] = dict(tree=str(tree), commit_as_given=rd(tree / 'FROZEN_COMMIT'), archive_sha256=rd(tree / 'FROZEN_ARCHIVE_SHA256'),
                   tree_files_sha256=rd(tree / 'FROZEN_TREE_SHA256'), cargo_lock_sha256=sha(tree / 'Cargo.lock'),
                   note='archive_sha256: sha256 of `git archive <commit> crates programs tools Cargo.toml Cargo.lock`; tree_files_sha256: sha256 of the sorted sha256sum list of every file under crates/, programs/, tools/ (fv_frz_tree.sh)')
m['library'] = dict(path=str(LIB), lean_toolchain=rd(LIB / 'lean-toolchain'), lean_toolchain_sha256=sha(LIB / 'lean-toolchain'),
                    lake_manifest_sha256=sha(LIB / 'lake-manifest.json'), lakefile_sha256=sha(LIB / 'lakefile.lean') if (LIB / 'lakefile.lean').exists() else None,
                    packages={p['name']: p.get('rev') for p in json.loads((LIB / 'lake-manifest.json').read_text()).get('packages', [])},
                    tools_check=rd(run / 'tools.tsv'))
for cp in sys.argv[3:]:
    cfg = json.loads(Path(cp).read_text())
    P = run / cfg['program']
    r = json.loads((P / 'result.json').read_text()) if (P / 'result.json').exists() else {}
    e = dict(config_file=Path(cp).name, config_sha256=sha(cp), root=cfg['roots'], features=cfg['features'],
             overflow_checks='off' if cfg['overflow_checks'] is False else 'on',
             overflow_env=('CARGO_PROFILE_RELEASE_OVERFLOW_CHECKS=false' if cfg['overflow_env_explicit'] else 'CARGO_PROFILE_RELEASE_OVERFLOW_CHECKS unset (release default false)'),
             opaque=cfg['opaque'], include=cfg['include'], aeneas_extra=cfg['aeneas_extra'], extra_env=cfg.get('extra_env', {}),
             tools=r.get('tools'), tool_hash_check=r.get('tool_hash_check'))
    for k in ('charon', 'aeneas'):
        f = P / k / ('%s_command.json' % k)
        e[k + '_command'] = json.loads(f.read_text()) if f.exists() else None
        e[k] = {x: y for x, y in r.get(k, {}).items() if x != 'outputs'}
    e['llbc_sha256'] = sha(P / 'charon' / 'out.llbc') if (P / 'charon' / 'out.llbc').exists() else None
    raw = P / 'aeneas' / 'raw' / cfg['ns']
    e['raw_lean_sha256'] = {p.name: sha(p) for p in sorted(raw.glob('*.lean'))}
    e['native'] = rd(P / 'native' / 'exit.txt')
    e['lean_version'] = rd(P / 'native' / 'lean-version.txt')
    feats = {}
    for t in ('host', 'sbf'):
        fs = C.features(run / 'tree' / ('%s-%s-pkgfeatures.txt' % (cfg['program'], t)))
        feats[t] = {p: sorted(fs.get(p, set())) for p in cfg['packages']}
    e['resolved_features'] = feats
    e['resolved_features_source'] = 'cargo tree -e normal --prefix none -f {p}|{f} (files tree/%s-{host,sbf}-pkgfeatures.txt; full -e features trees beside them)' % cfg['program']
    e['gates'] = {}
    for g in sorted((run / 'gates').glob('*-%s*.txt' % cfg['program'])) + sorted((run / 'gates').glob('*-both.txt')):
        lines = [l for l in g.read_text(errors='replace').splitlines() if l.startswith('gate ')]
        if lines: e['gates'][g.name] = lines[-1]
    m[cfg['program']] = e
m['constants'] = json.loads((run / 'constants.json').read_text()) if (run / 'constants.json').exists() else None
m['steps'] = (run / 'steps.tsv').read_text().splitlines() if (run / 'steps.tsv').exists() else None
m['scripts_sha256'] = {p.name: sha(p) for p in sorted(B.iterdir()) if p.is_file()}
(run / 'MANIFEST.json').write_text(json.dumps(m, indent=1) + '\n')
print('MANIFEST.json written: %d keys' % len(m))
