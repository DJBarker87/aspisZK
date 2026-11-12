#!/usr/bin/env python3
"""X1b item H: every `cfg(... target_os ...)` site in the four crates' sources (Rust files and manifests), the item
it gates (the next non-attribute line), the branch (SBF-only or host-only), and whether that item's name, under its module (file stem), occurs in the
emission's Funs.lean / Types.lean (a host build: a host-only item that occurs there is translated although the SBF
program does not contain it; an SBF-only item never occurs there). Reachability is read from the emission (Charon
translates only what the single entry reaches), so "in emission" is "reached from the entry in the host build".
usage: fv_x1b_targetos.py <tree> <raw emission dir>   (prints TSV)"""
import re, sys
from pathlib import Path
T, R = Path(sys.argv[1]), Path(sys.argv[2])
lean = (R / 'Funs.lean').read_text() + (R / 'Types.lean').read_text()
print('file\tline\tcfg\tbranch\tgated item\tname\tin emission')
for d in ('crates/aspis-core', 'crates/aspis-statement', 'crates/aspis-r1-cost-probe', 'programs/r1-cost-probe'):
    for p in sorted((T / d).rglob('*')):
        if p.suffix not in ('.rs', '.toml') or 'target' in p.parts: continue
        L = p.read_text(errors='replace').split('\n')
        for i, l in enumerate(L):
            m = re.search(r'cfg\((.*target_os.*?)\)\]?\s*$', l) or re.search(r"cfg\((.*target_os[^']*)\)", l)
            if not m: continue
            branch = 'host only' if 'not(target_os' in l else 'SBF only'
            j = i + 1
            while j < len(L) and (L[j].strip().startswith('#[') or L[j].strip().startswith('//') or not L[j].strip()): j += 1
            item = L[j].strip() if j < len(L) else ''
            n = re.search(r'\b(?:fn|mod|struct|enum|const|static|type|trait)\s+([A-Za-z_][A-Za-z0-9_]*)', item)
            u = re.search(r'\buse\s+.*?([A-Za-z_][A-Za-z0-9_]*)\s*;', item)
            name = n.group(1) if n else (u.group(1) if u else '')
            if p.suffix == '.toml': name, item = '', item + ' (manifest: dependency table)'
            stem = p.parent.name if p.stem in ('lib', 'mod') else p.stem
            if p.stem == 'lib': pat = r'(?:^|[\s(.])' + re.escape(name) + r'\.'          # a crate-root module: its path prefix
            elif name == stem: pat = r'\.' + re.escape(name) + r'\.'
            else: pat = r'\.' + re.escape(stem) + r'\.(?:[A-Za-z0-9_]+\.)*' + re.escape(name) + r'\b'
            hit = ('yes' if re.search(pat, lean) else 'no') if name else 'n/a'
            print('%s\t%d\t%s\t%s\t%s\t%s\t%s' % (p.relative_to(T), i + 1, m.group(1)[:90], branch, item[:110], name, hit))
