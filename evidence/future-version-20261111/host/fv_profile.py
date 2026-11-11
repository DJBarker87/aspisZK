#!/usr/bin/env python3
"""Future-version experiment: cost inventory from a LiteSVM register trace.

usage: fv_profile.py <linked-unstripped.so> <trace.regs> <program-cu> <out.json>

Every executed SBF instruction costs one compute unit; syscalls add their own
charges. The trace has 12 little-endian u64 per executed instruction (r0..r10,
then pc as an instruction index into .text). This tool attributes each executed
instruction three ways:

  dynamic   the call stack of outlined functions (from call/exit instructions),
            giving inclusive and self instruction counts and call counts;
  inline    the DWARF inline chain of its address (addr2line -i), giving, for
            every source function, the instructions executed inside it wherever
            it was inlined ("chain-inclusive");
  line      its innermost source line.

The syscall charge is program CU minus executed instructions. Attribution
evidence only; it changes nothing and proves nothing.
"""
import array, bisect, collections, json, re, struct, subprocess, sys


def u16(b, o): return struct.unpack_from('<H', b, o)[0]
def u32(b, o): return struct.unpack_from('<I', b, o)[0]
def u64(b, o): return struct.unpack_from('<Q', b, o)[0]


def sections(data):
    assert data[:4] == b'\x7fELF' and data[4] == 2 and data[5] == 1
    shoff, shentsize, shnum, shstrndx = u64(data, 0x28), u16(data, 0x3a), u16(data, 0x3c), u16(data, 0x3e)
    secs = []
    for i in range(shnum):
        o = shoff + i * shentsize
        secs.append(dict(name_off=u32(data, o), type=u32(data, o + 4), addr=u64(data, o + 0x10),
                         offset=u64(data, o + 0x18), size=u64(data, o + 0x20), link=u32(data, o + 0x28)))
    strtab = secs[shstrndx]
    for s in secs:
        n = data[strtab['offset'] + s['name_off']:]
        s['name'] = n[:n.index(b'\0')].decode()
    return secs


def functions(data, secs):
    out = set()
    for s in secs:
        if s['type'] != 2:
            continue
        st = secs[s['link']]
        for o in range(s['offset'], s['offset'] + s['size'], 24):
            name_off, info, value, size = u32(data, o), data[o + 4], u64(data, o + 8), u64(data, o + 16)
            if info & 0xf == 2 and size:
                n = data[st['offset'] + name_off:]
                out.add((value, size, n[:n.index(b'\0')].decode('utf-8', 'replace')))
    return sorted(out)


ESC = {'$LT$': '<', '$GT$': '>', '$u20$': ' ', '$C$': ',', '$RF$': '&', '$BP$': '*', '$LP$': '(', '$RP$': ')',
       '$u7b$': '{', '$u7d$': '}', '$u5b$': '[', '$u5d$': ']', '$u27$': "'", '$u3b$': ';', '$u2b$': '+', '$SP$': '@'}


def demangle(name):
    """Legacy Rust mangling (_ZN<len><ident>...E), hash segment dropped."""
    if not name.startswith('_ZN'):
        return name
    i, parts = 3, []
    while i < len(name) and name[i].isdigit():
        j = i
        while name[j].isdigit():
            j += 1
        n = int(name[i:j])
        parts.append(name[j:j + n])
        i = j + n
    if parts and re.fullmatch(r'h[0-9a-f]{16}', parts[-1]):
        parts.pop()
    s = '::'.join(parts)
    for k, v in ESC.items():
        s = s.replace(k, v)
    return s.replace('..', '::').lstrip('_') if s else name


def short(name):
    """Drop crate-path noise and generic arguments for grouping."""
    s = re.sub(r'<[^<>]*>', '', name)
    s = re.sub(r'<[^<>]*>', '', s)
    return s


def main():
    elf_path, regs_path, program_cu, out_path = sys.argv[1], sys.argv[2], int(sys.argv[3]), sys.argv[4]
    data = open(elf_path, 'rb').read()
    secs = sections(data)
    text = next(s for s in secs if s['name'] == '.text')
    funcs = functions(data, secs)
    starts = [f[0] for f in funcs]

    def func_of(addr):
        k = bisect.bisect_right(starts, addr) - 1
        if k >= 0 and addr < funcs[k][0] + funcs[k][1]:
            return funcs[k][2]
        return '?'

    regs = array.array('Q')
    with open(regs_path, 'rb') as f:
        regs.frombytes(f.read())
    assert len(regs) % 12 == 0
    pcs = regs[11::12]
    n = len(pcs)
    tbytes = data[text['offset']:text['offset'] + text['size']]
    addr_of = lambda pc: text['addr'] + 8 * pc

    # Dynamic call stack of outlined functions.
    self_count = collections.Counter()
    inclusive = collections.Counter()
    calls = collections.Counter()
    syscalls = collections.Counter()
    stack = []          # (function, instruction index at entry)
    frame_of = [None] * 0
    current = func_of(addr_of(pcs[0]))
    stack.append((current, 0))
    calls[current] += 1
    per_insn_func = []
    for i in range(n):
        pc = pcs[i]
        per_insn_func.append(current)
        self_count[current] += 1
        op = tbytes[8 * pc]
        nxt = pcs[i + 1] if i + 1 < n else None
        if op in (0x85, 0x8d):
            if nxt is not None and nxt != pc + 1:
                current = func_of(addr_of(nxt))
                stack.append((current, i + 1))
                calls[current] += 1
            elif op == 0x85:
                syscalls[u32(tbytes, 8 * pc + 4)] += 1
        elif op in (0x95, 0x9d):
            f, start = stack.pop()
            inclusive[f] += i + 1 - start
            current = stack[-1][0] if stack else '?'
    while stack:
        f, start = stack.pop()
        inclusive[f] += n - start

    # Static inline chains and lines for every executed address.
    count_pc = collections.Counter(pcs)
    unique = sorted(count_pc)
    proc = subprocess.run(['addr2line', '-e', elf_path, '-a', '-f', '-i'], input='\n'.join(hex(addr_of(p)) for p in unique),
                          capture_output=True, text=True, check=True)
    chains, cur = {}, None
    lines = proc.stdout.split('\n')
    k = 0
    while k < len(lines):
        line = lines[k]
        if line.startswith('0x'):
            cur = int(line, 16)
            chains[cur] = []
            k += 1
        elif line and cur is not None and k + 1 < len(lines):
            chains[cur].append((demangle(line), lines[k + 1].split(' (discriminator')[0]))
            k += 2
        else:
            k += 1
    chain_inclusive = collections.Counter()
    innermost = collections.Counter()
    by_line = collections.Counter()
    mapped = 0
    for p in unique:
        c = count_pc[p]
        chain = chains.get(addr_of(p), [])
        if chain and not chain[0][1].startswith('??'):
            mapped += c
        seen = set()
        for fn, _ in chain:
            s = short(fn)
            if s not in seen:
                seen.add(s)
                chain_inclusive[s] += c
        if chain:
            innermost[short(chain[0][0])] += c
            by_line[chain[0][1]] += c

    # Chain-inclusive counts restricted to each dynamic (outlined) function.
    within = collections.defaultdict(collections.Counter)
    for i in range(n):
        chain = chains.get(addr_of(pcs[i]), [])
        f = short(demangle(per_insn_func[i]))
        seen = set()
        for fn, _ in chain:
            s = short(fn)
            if s not in seen:
                seen.add(s)
                within[f][s] += 1

    top = lambda c, m: [[k, v] for k, v in c.most_common(m)]
    out = dict(
        elf=elf_path, trace=regs_path, program_cu=program_cu, executed_instructions=n,
        syscall_charge=program_cu - n, mapped_to_source_line=mapped, mapped_fraction=mapped / n,
        syscalls={hex(k): v for k, v in syscalls.most_common()},
        dynamic_inclusive=top(collections.Counter({short(demangle(k)): v for k, v in inclusive.items()}), 80),
        dynamic_self=top(collections.Counter({short(demangle(k)): v for k, v in self_count.items()}), 80),
        dynamic_calls=top(collections.Counter({short(demangle(k)): v for k, v in calls.items()}), 80),
        chain_inclusive=top(chain_inclusive, 150),
        innermost=top(innermost, 100),
        lines=top(by_line, 200),
        within={f: top(c, 40) for f, c in sorted(within.items(), key=lambda kv: -sum(1 for _ in kv[1])) if self_count_total(f, self_count) > n // 400},
    )
    json.dump(out, open(out_path, 'w'), indent=1)
    print(f'executed instructions {n}; program CU {program_cu}; syscall charge {program_cu - n}; mapped {mapped / n:.4f}')


def self_count_total(short_name, self_count):
    return sum(v for k, v in self_count.items() if short(demangle(k)) == short_name)


if __name__ == '__main__':
    main()
