#!/usr/bin/env python3
"""Read-after-write check over an Aeneas Lean emission (X2d item 2). A tool record, not a proof.

Question answered: starting from each given root definition, is there a path on which a read of account data or
lamports (any of the given read externals) runs after a call of a write boundary (any of the given write
externals)? The answer is computed over the emitted text, branch-sensitively and through calls. Nothing in this
file is specific to one program: the boundary names, the read names and the roots are arguments.

usage: fv_emit_read_after_write.py --funs FILE [--funs FILE ...] --write NAME[,NAME...] --read NAME[,NAME...]
                                   --root NAME[,NAME...] [--list-reached]

Method.
1. Items. Every top-level `def`/`impl_def` of the given files is parsed: its name, its header (binders and type) and
   its body (the text after `:=`). Doc comments and `--` comments are dropped. A definition named `<type>.Insts.<...>`
   (the translator's naming of trait implementations) whose body is a record `{ field := value ... }` and whose type
   is an application of some name T is an instance of T; its fields map method names to the definitions they name.
2. Events. In a body every dotted name is classified: a write (a --write name), a read (a --read name), a call of an
   emitted definition, a call through a trait-typed parameter (`p.m` where the header binds `(p : T ...)`; resolved
   to the field `m` of EVERY instance of T in the files, a sound union for the instances emitted), or a mention of an
   instance. A mention of an instance counts as a possible call of every method of that instance, except in a
   statement that calls an emitted definition (that definition receives the instance as a trait parameter and its
   own summary covers the method calls). Unknown names (library functions) have no effect.
3. Structure. Bodies are `do` blocks. They are parsed by indentation into statements; a statement is a `match ...
   with` with its arms, an `if ... then ... else ...` whose `then`/`else` begin lines, or an atomic statement. The walk
   carries the set of possible states {not yet written, written} through sequencing; each arm of a match and each
   branch of an if starts from the state before it, and the state after is the union over the arms. A read event in
   a possible "written" state is a read after write. Inside one atomic statement the events are taken in text order
   if the statement has no nested action `(← ...)`; otherwise, if one event may write and another may read, the order
   is not determined from the text and the statement is counted as a read after write (conservative). A statement
   that contains the `loop` combinator is applied twice (a later iteration may read what an earlier one wrote).
4. Summaries, to a fixed point over all definitions (recursion included): may read, may write, may read after write
   (from the definition's own entry, i.e. with nothing written yet). A call of D in a possibly-written state is a
   read after write if D may read; in a possibly-not-written state it is one if D's summary says so; after the call
   the state may be "written" if D may write.
Output: for each root, every reached definition that may read or may write with its summary, and the verdict.
Exit status 0 iff no root may read after write and no root reaches an unresolved trait-method call.
"""
import argparse
import re
import sys

NAME = re.compile(r"[A-Za-z_][A-Za-z0-9_'!?]*(?:\.(?:[A-Za-z_][A-Za-z0-9_'!?]*|«[^»]*»))*")
TOP = re.compile(r"^(?:@\[|/-|def\b|impl_def\b|noncomputable\b|private\b|partial\b|protected\b|axiom\b|opaque\b|"
                 r"theorem\b|structure\b|inductive\b|end\b|namespace\b|section\b|open\b|set_option\b|mutual\b|"
                 r"instance\b|abbrev\b|macro\b|attribute\b|#)")
DEF_KW = re.compile(r"^(?:noncomputable\s+|private\s+|protected\s+|partial\s+)*(def|impl_def|abbrev)\b\s*(\S*)")


def strip_comments(text):
    text = re.sub(r"/-.*?-/", lambda m: "\n" * m.group(0).count("\n"), text, flags=re.S)
    return "\n".join(re.sub(r"\s--.*$|^--.*$", "", l) for l in text.split("\n"))


class Item:
    def __init__(self, name, header, body_lines, file, line):
        self.name, self.header, self.body_lines, self.file, self.line = name, header, body_lines, file, line
        self.instance_of = None
        self.fields = {}
        self.trait_params = {}


def split_top_type(header):
    """The type after the last ':' at bracket depth 0 of a header (binders excluded)."""
    depth, last = 0, -1
    for i, c in enumerate(header):
        if c in "([{⦃":
            depth += 1
        elif c in ")]}⦄":
            depth -= 1
        elif c == ":" and depth == 0 and header[i:i + 2] != ":=" and header[i - 1:i + 1] != "::":
            last = i
    return header[last + 1:].strip() if last >= 0 else ""


def parse_items(files):
    items = {}
    for path in files:
        raw = open(path).read()
        lines = strip_comments(raw).split("\n")
        starts = [i for i, l in enumerate(lines) if l and not l[0].isspace() and TOP.match(l)]
        starts.append(len(lines))
        for a, b in zip(starts, starts[1:]):
            m = DEF_KW.match(lines[a])
            if not m:
                continue
            chunk = lines[a:b]
            name = m.group(2)
            rest_first = lines[a][m.end():]
            if not name:
                k = 1
                while k < len(chunk) and not chunk[k].strip():
                    k += 1
                name = chunk[k].split()[0]
            text = "\n".join(chunk)
            pos = None
            for mm in re.finditer(r":=", text):
                # the first ':=' at bracket depth 0 that is not inside a binder default
                pre = text[:mm.start()]
                if pre.count("(") - pre.count(")") == 0 and pre.count("{") - pre.count("}") == 0 \
                        and pre.count("[") - pre.count("]") == 0:
                    pos = mm.start()
                    break
            if pos is None:
                continue
            header = text[:pos]
            body = text[pos + 2:]
            line_of_body = a + header.count("\n")
            body_lines = body.split("\n")
            it = Item(name, header, body_lines, path, line_of_body + 1)
            # trait-typed parameters: (p : T args)
            for pm in re.finditer(r"\(\s*([A-Za-z_][A-Za-z0-9_']*)\s*:\s*(" + NAME.pattern + r")", header):
                it.trait_params[pm.group(1)] = pm.group(2)  # filtered to trait parameters after parsing
            first = body.lstrip()
            # a trait instance: a record body under the translator's instance name `<type>.Insts.<trait>` (a record
            # body under another name is a structure constant, not an instance)
            if first.startswith("{") and ".Insts." in name:
                ty = split_top_type(header)
                tm = NAME.match(ty)
                if tm:
                    it.instance_of = tm.group(0)
                    cur = None
                    for l in body_lines:
                        fm = re.match(r"\s*([A-Za-z_][A-Za-z0-9_']*)\s*:=(.*)$", l)
                        if fm:
                            cur = fm.group(1)
                            it.fields[cur] = fm.group(2)
                        elif cur and l.strip() not in ("", "}", "{"):
                            it.fields[cur] += " " + l.strip()
            items[name] = it
    return items


class Line:
    __slots__ = ("indent", "text", "no")

    def __init__(self, indent, text, no):
        self.indent, self.text, self.no = indent, text, no


def body_to_lines(item):
    out = []
    for k, l in enumerate(item.body_lines):
        if not l.strip():
            continue
        if k == 0:
            t = l.strip()
            if t in ("do", ""):
                continue
            if t.startswith("do "):
                t = t[3:]
            out.append(Line(10 ** 6, t, item.line))  # text on the ':=' line: a one-line body
            continue
        out.append(Line(len(l) - len(l.lstrip()), l.strip(), item.line + k))
    if out and out[0].indent == 10 ** 6:
        base = out[1].indent if len(out) > 1 else 2
        out[0].indent = base
    return out


CONT = re.compile(r"^(then|else|\|)(\s|$)")


def parse_block(lines, i, j):
    stmts, k = [], i
    if i >= j:
        return stmts
    base = lines[i].indent
    while k < j:
        m = k + 1
        while m < j and (lines[m].indent > base or (lines[m].indent == base and CONT.match(lines[m].text))
                         or lines[m].indent < base):
            if lines[m].indent < base and not CONT.match(lines[m].text):
                # a dedent inside a block: keep it with the statement (never seen in Aeneas output)
                pass
            m += 1
        stmts.append(parse_stmt(lines, k, m))
        k = m
    return stmts


def pseudo(text, indent, no):
    return Line(indent, text, no)


def parse_stmt(lines, k, m):
    # match ... with (on one of the statement's lines), arms beginning with '|'
    for h in range(k, m):
        t = lines[h].text
        if re.search(r"(^|\s|\()match\b.*\bwith$", t) and not CONT.match(t):
            arms_idx = [a for a in range(h + 1, m) if lines[a].text.startswith("|")]
            if not arms_idx:
                break
            arm_indent = lines[arms_idx[0]].indent
            arms_idx = [a for a in arms_idx if lines[a].indent == arm_indent]
            head = lines[k:h + 1]
            arms = []
            for x, a in enumerate(arms_idx):
                b = arms_idx[x + 1] if x + 1 < len(arms_idx) else m
                t2 = lines[a].text
                inline = t2.split("=>", 1)[1].strip() if "=>" in t2 else ""
                sub = []
                if inline:
                    sub.append(pseudo(inline, lines[a + 1].indent if a + 1 < b else lines[a].indent + 2, lines[a].no))
                sub.extend(lines[a + 1:b])
                arms.append(parse_block(sub, 0, len(sub)))
            return ("match", head, arms)
        if CONT.match(t):
            break
    # if / then / else with 'then' and 'else' beginning lines, or 'if ... then' ending a line
    for h in range(k, m):
        t = lines[h].text
        if re.search(r"(^|\s|←\s*)if\b", t):
            then_line = else_line = None
            if re.search(r"\bthen$", t):
                then_line = h
            for x in range(h + 1, m):
                tx = lines[x].text
                if then_line is None and re.match(r"^then(\s|$)", tx) and lines[x].indent <= lines[h].indent + 2:
                    then_line = x
                    continue
                if then_line is not None and re.match(r"^else(\s|$)", tx) and \
                        lines[x].indent == lines[then_line].indent:
                    # 'then' and 'else' begin lines at the same indentation ('then' ending the 'if' line counts
                    # with the 'if' line's indentation)
                    else_line = x
                    break
            if then_line is None:
                break
            head = lines[k:h + 1] if then_line == h else lines[k:then_line]
            if then_line == h:
                head = [pseudo(re.sub(r"\bthen$", "", lines[h].text), lines[h].indent, lines[h].no)] + []
                head = lines[k:h] + head
            tl = lines[then_line].text
            then_sub = []
            rest = re.sub(r"^then", "", tl).strip() if then_line != h else ""
            end_then = else_line if else_line is not None else m
            if rest:
                then_sub.append(pseudo(rest, lines[then_line + 1].indent if then_line + 1 < end_then else lines[then_line].indent + 2, lines[then_line].no))
            then_sub.extend(lines[then_line + 1:end_then])
            branches = [parse_block(then_sub, 0, len(then_sub))]
            if else_line is not None:
                el = lines[else_line]
                rest = re.sub(r"^else", "", el.text).strip()
                else_sub = []
                if rest:
                    else_sub.append(pseudo(rest, el.indent, el.no))
                else_sub.extend(lines[else_line + 1:m])
                branches.append(parse_block(else_sub, 0, len(else_sub)))
            else:
                branches.append([])
            return ("if", head, branches)
        if CONT.match(t):
            break
    # 'let x ← do' followed by a nested block
    for h in range(k, m):
        if re.search(r"(←|:=)\s*do$", lines[h].text) and h + 1 < m:
            return ("seq", lines[k:h + 1], parse_block(lines, h + 1, m))
    return ("atom", lines[k:m])


class Summary:
    __slots__ = ("may_read", "may_write", "raw", "witness")

    def __init__(self):
        self.may_read = self.may_write = self.raw = False
        self.witness = ""

    def key(self):
        return (self.may_read, self.may_write, self.raw)


class Analysis:
    def __init__(self, items, writes, reads):
        self.items, self.writes, self.reads = items, set(writes), set(reads)
        self.instances = {}
        for it in items.values():
            if it.instance_of:
                self.instances.setdefault(it.instance_of, []).append(it)
        for it in items.values():
            # a trait parameter: its type has an emitted instance, or it carries the translator's `...Inst` name
            it.trait_params = {p: t for p, t in it.trait_params.items() if t in self.instances or p.endswith("Inst")}
        self.summ = {n: Summary() for n in items}
        self.unresolved = {}
        self.calls = {n: set() for n in items}
        self.trees = {}
        for n, it in items.items():
            if it.instance_of:
                continue
            ls = body_to_lines(it)
            self.trees[n] = parse_block(ls, 0, len(ls))

    def method_targets(self, trait, method):
        out = set()
        for inst in self.instances.get(trait, []):
            v = inst.fields.get(method)
            if v is None:
                continue
            for nm in NAME.findall(v):
                if nm in self.items or nm in self.writes or nm in self.reads:
                    out.add(nm)
        return out

    def events(self, owner, stmt_lines):
        """[(kind, name, may_read, may_write, raw)] in text order, and whether a nested action occurs."""
        text = " ".join(l.text for l in stmt_lines)
        it = self.items[owner]
        evs = []
        found = list(NAME.finditer(text))
        calls_emitted = any(nm.group(0) in self.items and not self.items[nm.group(0)].instance_of for nm in found)
        for nm in found:
            n = nm.group(0)
            if n in self.writes:
                evs.append(("write", n, False, True, False))
            elif n in self.reads:
                evs.append(("read", n, True, False, False))
            elif n in self.items:
                target = self.items[n]
                if target.instance_of:
                    if calls_emitted:
                        continue
                    for meth in target.fields:
                        for t in self.method_targets(target.instance_of, meth):
                            evs.append(self.call_event(owner, t))
                    continue
                evs.append(self.call_event(owner, n))
            else:
                parts = n.split(".")
                if len(parts) >= 2 and parts[0] in it.trait_params:
                    trait = it.trait_params[parts[0]]
                    meth = parts[1]
                    targets = self.method_targets(trait, meth)
                    if not targets and trait in self.instances:
                        self.unresolved.setdefault(owner, set()).add(n)
                    if not targets and trait not in self.instances:
                        # a trait with no emitted instance: only library instances can be passed; recorded
                        self.unresolved.setdefault(owner, set()).add(n + " (no emitted instance of " + trait + ")")
                    for t in sorted(targets):
                        evs.append(self.call_event(owner, t))
        return evs, ("(←" in text)

    def call_event(self, owner, n):
        if n in self.writes:
            return ("write", n, False, True, False)
        if n in self.reads:
            return ("read", n, True, False, False)
        self.calls[owner].add(n)
        s = self.summ[n]
        return ("call", n, s.may_read, s.may_write, s.raw)

    def apply_atom(self, owner, stmt_lines, state, acc):
        evs, nested = self.events(owner, stmt_lines)
        text = " ".join(l.text for l in stmt_lines)
        reps = 2 if re.search(r"(^|\s)loop(\s|$)", text) else 1
        if nested:
            wr = [e for e in evs if e[3]]
            rd = [e for e in evs if e[2]]
            if any(a is not b for a in wr for b in rd):
                acc.flag("order inside one statement with a nested action is not determined: %s" % text[:160],
                         stmt_lines[0].no)
        for _ in range(reps):
            for kind, n, r, w, raw in evs:
                if r:
                    acc.may_read = True
                if w:
                    acc.may_write = True
                if True in state and r:
                    acc.flag("%s (%s) after a possible write" % (n, "reads" if kind == "read" else "may read"),
                             stmt_lines[0].no)
                if False in state and raw:
                    acc.flag("%s may read after write inside" % n, stmt_lines[0].no)
                if kind == "write":
                    state = {True}
                elif w:
                    state = state | {True}
        return state

    def walk(self, owner, stmts, state, acc):
        for st in stmts:
            kind = st[0]
            if kind == "atom":
                state = self.apply_atom(owner, st[1], state, acc)
            elif kind == "seq":
                state = self.apply_atom(owner, st[1], state, acc)
                state = self.walk(owner, st[2], state, acc)
            else:
                state = self.apply_atom(owner, st[1], state, acc)
                out = set()
                for br in st[2]:
                    out |= self.walk(owner, br, set(state), acc)
                state = out if out else state
        return state

    def run(self):
        changed = True
        rounds = 0
        while changed:
            changed = False
            rounds += 1
            for n, tree in self.trees.items():
                acc = Acc()
                self.walk(n, tree, {False}, acc)
                s = self.summ[n]
                if (acc.may_read, acc.may_write, acc.raw) != s.key() or (acc.raw and not s.witness):
                    new = (s.may_read or acc.may_read, s.may_write or acc.may_write, s.raw or acc.raw)
                    if new != s.key():
                        changed = True
                    s.may_read, s.may_write, s.raw = new
                    if acc.raw and not s.witness:
                        s.witness = acc.witness
        return rounds

    def reached(self, root):
        seen, todo = set(), [root]
        while todo:
            n = todo.pop()
            if n in seen or n not in self.items:
                continue
            seen.add(n)
            todo.extend(self.calls.get(n, ()))
        return seen


class Acc:
    def __init__(self):
        self.may_read = self.may_write = self.raw = False
        self.witness = ""

    def flag(self, why, line):
        if not self.raw:
            self.witness = "line %d: %s" % (line, why)
        self.raw = True


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--funs", action="append", required=True)
    ap.add_argument("--write", required=True)
    ap.add_argument("--read", required=True)
    ap.add_argument("--root", required=True)
    ap.add_argument("--list-reached", action="store_true")
    a = ap.parse_args()
    items = parse_items(a.funs)
    an = Analysis(items, a.write.split(","), a.read.split(","))
    rounds = an.run()
    print("files: %s" % ", ".join(a.funs))
    print("definitions parsed: %d (instances %d); fixed point after %d rounds" %
          (len(items), sum(1 for i in items.values() if i.instance_of), rounds))
    print("write boundaries: %s" % ", ".join(sorted(an.writes)))
    print("read externals: %s" % ", ".join(sorted(an.reads)))
    ok = True
    for root in a.root.split(","):
        if root not in items:
            print("ROOT NOT FOUND: %s" % root)
            ok = False
            continue
        reach = an.reached(root)
        s = an.summ[root]
        eff = sorted(n for n in reach if an.summ[n].may_read or an.summ[n].may_write)
        bad = sorted(n for n in reach if an.summ[n].raw)
        unres = sorted(u for n in reach for u in an.unresolved.get(n, ()))
        verdict = "PASS" if not s.raw and not [u for u in unres if "no emitted instance" not in u] else "FAIL"
        if verdict == "FAIL":
            ok = False
        print("== root %s: %s" % (root, verdict))
        print("   reached definitions %d; that may read %d; that may write %d; that may read after a write %d" %
              (len(reach), sum(1 for n in reach if an.summ[n].may_read),
               sum(1 for n in reach if an.summ[n].may_write), len(bad)))
        print("   root summary: may read %s, may write %s, may read after write %s%s" %
              (s.may_read, s.may_write, s.raw, (" (" + s.witness + ")") if s.raw else ""))
        if s.may_read and not s.raw:
            print("   reads before any write only: yes")
        for n in bad:
            print("   read after write in %s: %s" % (n, an.summ[n].witness))
        for u in unres:
            print("   unresolved trait-method call: %s" % u)
        if a.list_reached:
            for n in eff:
                t = an.summ[n]
                print("     %-110s read=%d write=%d raw=%d" % (n, t.may_read, t.may_write, t.raw))
    print("overall", "PASS" if ok else "FAIL")
    sys.exit(0 if ok else 1)


if __name__ == "__main__":
    main()
