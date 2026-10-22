#!/usr/bin/env python3
"""Read-only recursive Lean .olean header closure check for imports in a source file."""
from pathlib import Path
import argparse, hashlib, json, os, re, struct, sys

def imports(path):
    b = path.read_bytes()
    if b[:5] != b'olean':
        raise ValueError(f'not an olean: {path}')
    base, root = struct.unpack_from('<QQ', b, 80)
    def u(o): return struct.unpack_from('<Q', b, o)[0]
    def name(p):
        if p & 1:
            if p != 1: raise ValueError(f'bad null Lean name pointer {p}')
            return ''
        o = p - base
        tag = b[o + 7]
        prefix = name(u(o + 8))
        if tag == 1:
            q = u(o + 16) - base
            tail = b[q + 32:b.index(0, q + 32)].decode()
        elif tag == 2:
            tail = str(u(o + 16))
        else:
            raise ValueError(f'unknown Lean name tag {tag}')
        return prefix + '.' + tail if prefix else tail
    arr = u(root - base + 8) - base
    return list(dict.fromkeys(name(u(u(arr + 24 + 8*i) - base + 8))
                              for i in range(u(arr + 8))))

def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('source', type=Path)
    ap.add_argument('--lean-lib', type=Path, required=True)
    ap.add_argument('--output', type=Path)
    args = ap.parse_args()
    roots = [Path(os.path.realpath(p)) for p in os.environ['LEAN_PATH'].split(':') if p]
    builtin = Path(os.path.realpath(args.lean_lib))
    seeds = re.findall(r'^import\s+([A-Za-z0-9_.]+)', args.source.read_text(), re.M)
    queue = list(seeds); seen = {}; missing = []
    while queue:
        module = queue.pop()
        if module in seen: continue
        rel = Path(*module.split('.')).with_suffix('.olean')
        path = next((r / rel for r in roots if (r / rel).is_file()), None)
        is_builtin = False
        if path is None and (builtin / rel).is_file():
            path = builtin / rel; is_builtin = True
        if path is None:
            missing.append(module); continue
        ds = imports(path)
        seen[module] = {'path': str(path), 'sha256': hashlib.sha256(path.read_bytes()).hexdigest(),
                        'builtin': is_builtin, 'imports': ds}
        queue.extend(ds)
    result = {'source': str(args.source), 'seed_imports': seeds, 'modules': len(seen),
              'missing': sorted(set(missing)), 'owners': seen}
    encoded = json.dumps(result, indent=2) + '\n'
    if args.output: args.output.write_text(encoded)
    print(json.dumps({'modules': len(seen), 'missing': sorted(set(missing))}))
    return 0 if not missing else 1
if __name__ == '__main__': raise SystemExit(main())
