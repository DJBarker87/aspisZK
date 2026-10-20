#!/usr/bin/env python3
"""Attach source lines to ELF slots of the measured (no debug info) build using
the line-tables-only build. A slot is mapped only if its function exists in both
builds with equal size and equal instructions, masking the immediates of internal
calls and lddw (layout-dependent); otherwise the site keeps its ELF location only.
usage: map_lines.py <linked.elf> <debug linked.elf> <addrs.json: [hex addr...]> <out.json>
out: {addr: {mapped: bool, function, frames: [[func, file:line]...] (innermost first)}}"""
import json, subprocess, sys, os, struct, bisect, re
BASE = lambda n: re.sub(r'17h[0-9a-f]{16}E$', '', n)
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import sbf_slack as S
L, D, ADDRS, OUT = sys.argv[1:5]
def load(p):
    data = open(p, 'rb').read(); secs = S.elf_sections(data)
    tx = next(s for s in secs if s['name'] == '.text')
    text = data[tx['offset']:tx['offset'] + tx['size']]
    funcs = [(v, sz, n) for v, sz, n in S.elf_functions(data, secs) if tx['addr'] <= v < tx['addr'] + tx['size']]
    return text, tx['addr'], funcs
lt, la, lf = load(L); dt, da, df = load(D)
dby = {}
for v, sz, n in df: dby.setdefault(BASE(n), []).append((v, sz))
def masked(text, base, v, sz):
    out = bytearray(text[v - base:v - base + sz]); i = 0
    while i < len(out):
        op = out[i]
        if op == 0x85 or op == 0x18:
            out[i + 4:i + 8] = b'\0\0\0\0'
            if op == 0x18 and i + 16 <= len(out): out[i + 12:i + 16] = b'\0\0\0\0'; i += 8
        i += 8
    return bytes(out)
starts = [f[0] for f in lf]
addrs = json.load(open(ADDRS)); res = {}; query = []
match_cache = {}
for a in addrs:
    x = int(a, 16); i = bisect.bisect_right(starts, x) - 1
    if i < 0 or x >= lf[i][0] + lf[i][1]: res[a] = dict(mapped=False, reason='no function'); continue
    v, sz, n = lf[i]
    if n not in match_cache:
        cand = [c for c in dby.get(BASE(n), []) if c[1] == sz]
        m = None
        for dv, dsz in cand:
            if masked(lt, la, v, sz) == masked(dt, da, dv, dsz): m = dv; break
        match_cache[n] = m
    m = match_cache[n]
    if m is None: res[a] = dict(mapped=False, function=n, reason='function differs between builds'); continue
    res[a] = dict(mapped=True, function=n, mapped_by='name-without-hash, equal size, equal masked instructions', debug_addr=hex(m + (x - v))); query.append((a, m + (x - v)))
for k in range(0, len(query), 2000):
    chunk = query[k:k + 2000]
    p = subprocess.run(['addr2line', '-f', '-i', '-a', '-e', D] + [hex(q[1]) for q in chunk], capture_output=True, text=True, check=True)
    blocks = p.stdout.split('0x'); blocks = [b for b in blocks if b.strip()]
    # output: address line, then (func, file:line) pairs per inline frame
    lines = p.stdout.splitlines(); j = 0; cur = None; out = {}
    order = iter(chunk)
    for line in lines:
        if line.startswith('0x') and all(c in '0123456789abcdefx' for c in line.strip()):
            cur = next(order)[0]; out[cur] = []; pending = None
        elif pending is None:
            pending = line
        else:
            out[cur].append([pending, line.replace('/home/dombarker/project-offloads/codex-cx-cu-bound5-20261020/src/', '')]); pending = None
    for a, fr in out.items(): res[a]['frames'] = fr
json.dump(res, open(OUT, 'w'), indent=0)
print(sum(1 for r in res.values() if r.get('mapped')), 'mapped of', len(res))
