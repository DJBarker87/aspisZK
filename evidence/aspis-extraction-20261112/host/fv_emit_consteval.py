#!/usr/bin/env python3
"""X7: the values of the compile-time constants that the verifier program's emission computes by call, obtained from
a build. Runs INSIDE the fv_slot.sh scope of fv_emit_job.sh (it runs rustc).

1. The two deployment ids (`AUDIT_POOL_PROGRAM`, `AUDIT_REGISTRY_PROGRAM` of programs/r1-cost-probe/src/r1_pool_adapter.rs):
   in the emission they are definitions that call `deployment_ids.deployment_id` on the string of the build
   environment. A host program is compiled by rustc (nightly-2026-09-17, the emission's toolchain) from the tree's own
   `deployment_ids.rs` (included by #[path], unchanged) and the two `static` items copied byte for byte from the
   tree's r1_pool_adapter.rs (attributes dropped), with the emission's environment (the config's extra_env). rustc
   evaluates the statics at compile time, as in the program build; the program prints them.
2. The loader ids: every `<module>::id` external of the SDK crate solana_sdk_ids in either emission (in the verifier
   program `bpf_loader_upgradeable::id`). Obtained two ways that must agree: (a) a host program compiled by the same
   rustc against the `solana_sdk_ids` rlib that the emission's cargo build produced (found under the Charon run's
   target dir, with every rlib directory there on the dependency search path),
   calling `<module>::id().to_bytes()`; (b) the base58 decoding (Python) of the `declare_id!` string in that crate's
   registry source. When (a) cannot link (Charon's rlibs are metadata stubs), (a') a one-file cargo package that
   depends on solana-sdk-ids at the tree's locked version (offline, started from the tree's Cargo.lock) is built and
   run. (b) alone is reported when neither builds.
3. A check against an independent decoding: the base58 decoding (Python) of each deployment-id string.
usage: fv_emit_consteval.py <tree> <run dir> <verifier config.json> <cargo target dir>   (writes <run>/constants.json)"""
import glob, json, os, re, subprocess, sys
from pathlib import Path

tree, run, cfg, tgt = Path(sys.argv[1]), Path(sys.argv[2]), json.loads(Path(sys.argv[3]).read_text()), Path(sys.argv[4])
work = run / 'consteval'
work.mkdir(parents=True, exist_ok=True)
RUSTC = ['env', 'PATH=/home/dombarker/.cargo/bin:/usr/bin:/bin', 'RUSTUP_TOOLCHAIN=nightly-2026-09-17', 'rustc']
A = '123456789ABCDEFGHJKLMNPQRSTUVWXYZabcdefghijkmnopqrstuvwxyz'


def b58(s):
    n = 0
    for ch in s:
        n = n * 58 + A.index(ch)
    raw = n.to_bytes((n.bit_length() + 7) // 8, 'big') if n else b''
    raw = b'\0' * (len(s) - len(s.lstrip('1'))) + raw
    return raw.hex()


res = {'method': __doc__.split('usage:')[0].strip()}
src = (tree / 'programs/r1-cost-probe/src/r1_pool_adapter.rs').read_text()
statics = re.findall(r'(?ms)^static (AUDIT_(?:POOL|REGISTRY)_PROGRAM): \[u8; 32\] = (deployment_ids::deployment_id\(.*?\));', src)
prog = ['#![allow(dead_code)]', '#[path = "%s"]' % (tree / 'programs/r1-cost-probe/src/deployment_ids.rs'), 'mod deployment_ids;']
for name, expr in statics:
    prog.append('static %s: [u8; 32] = %s;' % (name, expr))
prog.append('fn hex(b: &[u8; 32]) -> String { b.iter().map(|x| format!("{:02x}", x)).collect() }')
prog.append('fn main() {')
for name, _ in statics:
    prog.append('    println!("%s {}", hex(&%s));' % (name, name))
prog.append('}')
(work / 'ids.rs').write_text('\n'.join(prog) + '\n')
env = dict(os.environ)
env.update(cfg.get('extra_env', {}))
r = subprocess.run(RUSTC + ['--edition', '2021', '-O', '-o', str(work / 'ids'), str(work / 'ids.rs')], capture_output=True, text=True, env=env)
res['deployment_ids'] = dict(statics_found=[n for n, _ in statics], statics_text={n: e for n, e in statics}, rustc_exit=r.returncode,
                             rustc_stderr=r.stderr[-2000:], env={k: v for k, v in cfg.get('extra_env', {}).items()})
if r.returncode == 0:
    o = subprocess.run([str(work / 'ids')], capture_output=True, text=True).stdout
    vals = dict(l.split() for l in o.splitlines() if l.strip())
    res['deployment_ids']['values_from_build'] = vals
    chk = {}
    for name, expr in statics:
        var = re.search(r'option_env!\("([A-Z0-9_]+)"\)', expr).group(1)
        s = cfg.get('extra_env', {}).get(var)
        chk[name] = dict(env=var, string=s, python_base58=b58(s) if s else None, agrees=(b58(s) == vals.get(name)) if s else None)
    res['deployment_ids']['independent_check'] = chk
# ---- loader ids
names = set()
for prog_dir in sorted(run.glob('*/aeneas/raw/*/FunsExternal_Template.lean')):
    names |= set(re.findall(r'solana_sdk_ids\.([a-z0-9_]+)\.id\b', prog_dir.read_text()))
res['loader_ids'] = {}
srcdirs = sorted(glob.glob('/home/dombarker/.cargo/registry/src/*/solana-sdk-ids-*/src/lib.rs'))
lock = (tree / 'Cargo.lock').read_text()
ver = re.search(r'name = "solana-sdk-ids"\nversion = "([^"]+)"', lock).group(1)
lib = next((p for p in srcdirs if '/solana-sdk-ids-%s/' % ver in p), None)
libtext = Path(lib).read_text() if lib else ''
rlibs = sorted(glob.glob(str(tgt / '**/libsolana_sdk_ids-*.rlib'), recursive=True))
via = {}
if rlibs and names:
    # Charon's cargo build keeps each dependency's objects in its own directory (<target>/<triple>/release/build/<crate>/<hash>/out)
    dirs = sorted({str(Path(p).parent) for p in glob.glob(str(tgt / '**/*.rlib'), recursive=True)})
    lp = [x for d in dirs for x in ('-L', 'dependency=' + d)] + ['--extern', 'solana_sdk_ids=%s' % rlibs[0]]
    body = '\n'.join('    println!("%s {}", solana_sdk_ids::%s::id().to_bytes().iter().map(|x| format!("{:02x}", x)).collect::<String>());' % (n, n) for n in sorted(names))
    (work / 'loader.rs').write_text('fn main() {\n%s\n}\n' % body)
    r2 = subprocess.run(RUSTC + ['--edition', '2021', '-o', str(work / 'loader'), str(work / 'loader.rs')] + lp, capture_output=True, text=True)
    res['loader_rustc'] = dict(exit=r2.returncode, rlib=rlibs[0], stderr=r2.stderr[-1500:])
    if r2.returncode == 0:
        o = subprocess.run([str(work / 'loader')], capture_output=True, text=True).stdout
        via = dict(l.split() for l in o.splitlines() if l.strip())
if names and not via:
    # (a') Charon's rlibs are metadata stubs (rustc: "only metadata stub found"); build the SDK crate itself: a
    # one-file cargo package depending on solana-sdk-ids at the version of the tree's Cargo.lock (offline, from the
    # local registry), started from a copy of that Cargo.lock so every shared dependency keeps its locked version
    pk = work / 'sdkids'
    (pk / 'src').mkdir(parents=True, exist_ok=True)
    (pk / 'Cargo.toml').write_text('[package]\nname = "x7-sdkids"\nversion = "0.0.0"\nedition = "2021"\n[workspace]\n[dependencies]\nsolana-sdk-ids = "=%s"\n' % ver)
    (pk / 'Cargo.lock').write_text(lock)
    body = '\n'.join('    println!("%s {}", solana_sdk_ids::%s::id().to_bytes().iter().map(|x| format!("{:02x}", x)).collect::<String>());' % (n, n) for n in sorted(names))
    (pk / 'src' / 'main.rs').write_text('fn main() {\n%s\n}\n' % body)
    env2 = {k: v for k, v in os.environ.items() if k not in ('RUSTFLAGS', 'CARGO_TARGET_DIR')}
    env2.update(PATH='/home/dombarker/.cargo/bin:/usr/bin:/bin', RUSTUP_TOOLCHAIN='nightly-2026-09-17', CARGO_NET_OFFLINE='true', CARGO_TARGET_DIR=str(pk / 'target'))
    r3 = subprocess.run(['cargo', 'run', '--offline', '--release', '--quiet', '--manifest-path', str(pk / 'Cargo.toml')], capture_output=True, text=True, env=env2)
    lk = (pk / 'Cargo.lock').read_text() if (pk / 'Cargo.lock').exists() else ''
    res['loader_cargo'] = dict(exit=r3.returncode, stderr=r3.stderr[-1500:],
                               solana_sdk_ids_version=(re.search(r'name = "solana-sdk-ids"\nversion = "([^"]+)"', lk) or [None, None])[1],
                               solana_pubkey_version=(re.search(r'name = "solana-pubkey"\nversion = "([^"]+)"', lk) or [None, None])[1])
    if r3.returncode == 0:
        via = dict(l.split() for l in r3.stdout.splitlines() if l.strip())
    subprocess.run(['rm', '-rf', str(pk / 'target')])
for n in sorted(names):
    m = re.search(r'pub mod %s \{.*?declare_id!\("([1-9A-HJ-NP-Za-km-z]+)"\)' % re.escape(n), libtext, re.S)
    s = m.group(1) if m else None
    res['loader_ids'][n] = dict(sdk_crate='solana-sdk-ids %s' % ver, declare_id=s, python_base58=b58(s) if s else None,
                               value_from_build=via.get(n), agrees=(via.get(n) == b58(s)) if (s and n in via) else None)
(run / 'constants.json').write_text(json.dumps(res, indent=1) + '\n')
print(json.dumps({k: res[k] for k in ('deployment_ids', 'loader_ids')}, indent=1)[:3000])
