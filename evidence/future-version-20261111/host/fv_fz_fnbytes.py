#!/usr/bin/env python3
"""Naming cleanup (fz): function-by-function byte comparison of two unstripped SBF program ELFs. Reads only.

For every FUNC symbol defined in .text: its bytes (st_value, st_size), with the 32-bit immediate of every `call`
instruction (opcode byte 0x85) and both 32-bit immediate halves of every `lddw` (opcode 0x18, two 8-byte slots)
masked to zero. Functions are matched by legacy-demangled path without the hash segment; the control ELF's names
are first mapped through the rename map (old path -> new path, TSV, column 1 and 2, `::`-separated, `*` matching
any leading segments). Prints counts, every function present on one side only, and every matched function whose
masked bytes differ.

usage: fv_fz_fnbytes.py <control.so> <other.so> <rename_map.tsv>
"""
import re, struct, sys, hashlib


def elf_functions(path):
    data = open(path, 'rb').read()
    assert data[:4] == b'\x7fELF' and data[4] == 2 and data[5] == 1, 'ELF64 little-endian expected'
    shoff, = struct.unpack_from('<Q', data, 0x28)
    shentsize, shnum, shstrndx = struct.unpack_from('<HHH', data, 0x3a)
    secs = []
    for i in range(shnum):
        name, typ, flags, addr, off, size, link, info, align, entsize = struct.unpack_from('<IIQQQQIIQQ', data, shoff + i * shentsize)
        secs.append(dict(name=name, type=typ, addr=addr, off=off, size=size, link=link, entsize=entsize))
    shstr = secs[shstrndx]
    def secname(s):
        o = shstr['off'] + s['name']; e = data.index(b'\0', o); return data[o:e].decode()
    for s in secs: s['n'] = secname(s)
    text_i = next(i for i, s in enumerate(secs) if s['n'] == '.text')
    text = secs[text_i]
    sym = next(s for s in secs if s['type'] == 2)  # SHT_SYMTAB
    strtab = secs[sym['link']]
    res = {}
    for k in range(sym['size'] // 24):
        st_name, st_info, st_other, st_shndx, st_value, st_size = struct.unpack_from('<IBBHQQ', data, sym['off'] + 24 * k)
        if st_info & 0xf != 2 or st_shndx != text_i or st_size == 0:
            continue
        o = strtab['off'] + st_name; e = data.index(b'\0', o); name = data[o:e].decode()
        start = text['off'] + (st_value - text['addr'])
        res.setdefault(name, []).append(bytes(data[start:start + st_size]))
    return res, text['size']


def mask(code):
    b = bytearray(code); i = 0
    while i + 8 <= len(b):
        op = b[i]
        if op == 0x85:
            b[i + 4:i + 8] = b'\0\0\0\0'; i += 8
        elif op == 0x18 and i + 16 <= len(b):
            b[i + 4:i + 8] = b'\0\0\0\0'; b[i + 12:i + 16] = b'\0\0\0\0'; i += 16
        else:
            i += 8
    return bytes(b)


def demangle(sym):
    """Legacy Rust mangling: _ZN <len><seg>... E; the trailing 17h<hash> segment is dropped. Others returned as is."""
    m = re.match(r'_ZN(.*)E$', sym)
    if not m:
        return sym
    s = m.group(1); segs = []; i = 0
    while i < len(s):
        j = i
        while j < len(s) and s[j].isdigit(): j += 1
        if j == i: return sym
        n = int(s[i:j]); segs.append(s[j:j + n]); i = j + n
    if segs and re.fullmatch(r'h[0-9a-f]{16}', segs[-1]): segs = segs[:-1]
    return '::'.join(segs)


def load_map(path):
    rules = []
    for line in open(path):
        if not line.strip() or line.startswith('#'): continue
        f = line.rstrip('\n').split('\t')
        if f[0] == 'old': continue
        rules.append((f[0], f[1]))
    return rules


def apply_map(name, rules):
    name = name.replace('..candidate..fused..', '..candidate..one_tx..')
    for old, new in rules:
        if old.startswith('(') or old.startswith('feature '): continue
        o = old.split('::'); n = new.split('::')
        segs = name.split('::')
        # match `o` as a contiguous run of segments ending at a segment boundary (prefix rename of a path)
        for i in range(len(segs) - len(o) + 1):
            if segs[i:i + len(o)] == o:
                segs = segs[:i] + n + segs[i + len(o):]
                name = '::'.join(segs)
                break
    return name


def main():
    a, b, mp = sys.argv[1:4]
    rules = load_map(mp)
    A, ta = elf_functions(a); B, tb = elf_functions(b)
    def keyed(F, mapped):
        out = {}
        for sym, bodies in F.items():
            k = demangle(sym)
            if mapped: k = apply_map(k, rules)
            out.setdefault(k, []).extend(mask(x) for x in bodies)
        return {k: sorted(v) for k, v in out.items()}
    KA = keyed(A, True); KB = keyed(B, False)
    both = sorted(set(KA) & set(KB)); oa = sorted(set(KA) - set(KB)); ob = sorted(set(KB) - set(KA))
    same = [k for k in both if KA[k] == KB[k]]; diff = [k for k in both if KA[k] != KB[k]]
    renamed = sum(1 for sym in A if apply_map(demangle(sym), rules) != demangle(sym))
    print(f'.text bytes: control {ta}, other {tb}')
    print(f'function symbols: control {sum(len(v) for v in A.values())} ({len(KA)} names), other {sum(len(v) for v in B.values())} ({len(KB)} names); control symbols renamed through the map: {renamed}')
    print(f'matched names {len(both)}; byte-identical after masking call/lddw immediates: {len(same)}; different: {len(diff)}; only in control: {len(oa)}; only in other: {len(ob)}')
    for k in oa: print('  only in control:', k[:200])
    for k in ob: print('  only in other:  ', k[:200])
    for k in diff: print('  bytes differ:   ', k[:200], [len(x) for x in KA[k]], '->', [len(x) for x in KB[k]])
    h = hashlib.sha256(); [h.update(k.encode() + b''.join(KB[k])) for k in sorted(KB)]
    print('masked function table sha256 (other):', h.hexdigest())
    sys.exit(0 if not (oa or ob or diff) else 1)


if __name__ == '__main__':
    main()
