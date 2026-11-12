#!/usr/bin/env python3
"""X6 check (c): a port patch changes no statement.

For each module present in <carried-src> and differing in <ported-src>:
  1. every declaration (theorem, lemma, def, abbrev, structure, instance, inductive, class, opaque, axiom, with
     attributes and modifiers) is cut into its statement: the text from the keyword to the first `:=`, `where` or
     line-initial `|` at bracket depth 0 (comments removed, whitespace kept byte-exact). The ordered list of
     (keyword, name, statement) must be identical in both files. Statements of declarations nested in a proof
     (a `have` is not a declaration) are not affected.
  2. every changed line (difflib over the two files) must not lie before the last line of the statement of the
     declaration that encloses it (the last line itself is covered by step 1); a changed line outside any declaration is reported as `header`
     (only import lines are accepted there, and each must be listed in <allowed-header-edits>).
  3. added lines must not contain: sorry, admit, native_decide, maxHeartbeats, maxRecDepth, set_option, axiom,
     decide (a `decide` already on the replaced line is not counted).
Modules absent from <ported-src> are listed as `removed` and must be listed in <allowed-removals>.
Prints one row per finding; exit 0 iff there is none.
Usage: fv_x6_stmtcheck.py <carried-src> <ported-src> <allowed-removals.txt> <allowed-header-edits.tsv> [module ...]
  (<allowed-header-edits.tsv>: rows `module<TAB>exact new line` (an allowed new header line, e.g. an added Mathlib
   import) and rows `ATTR<TAB>module<TAB>declaration<TAB>attribute` (an attribute that may be added to that one
   declaration) and rows `STMT<TAB>module<TAB>declaration` (a theorem whose statement text may change, class
   `statement text: Mathlib API rename`); without explicit modules, every .lean of carried-src)
  4. attribute lines: any added or removed line starting with `@[` or `attribute [` is a finding unless it is the
     same line with only an allowed attribute added (ATTR row, matched against the next declaration's name).
"""
import difflib, os, re, sys

KW = r"(theorem|lemma|def|abbrev|structure|instance|inductive|class|opaque|axiom)"
HEAD = re.compile(r"^(?:@\[[^\]]*\]\s*)*(?:(?:private|protected|noncomputable|partial|unsafe|nonrec|public|scoped|local)\s+)*"
                  + KW + r"\b(.*)$")


def strip_comments(s):
    out, i, n, depth = [], 0, len(s), 0
    while i < n:
        if s.startswith("/-", i):
            depth += 1; i += 2; continue
        if depth and s.startswith("-/", i):
            depth -= 1; i += 2; continue
        if depth:
            out.append("\n" if s[i] == "\n" else " "); i += 1; continue
        if s.startswith("--", i):
            j = s.find("\n", i)
            j = n if j < 0 else j
            out.append(" " * (j - i)); i = j; continue
        out.append(s[i]); i += 1
    return "".join(out)


def decls(text):
    """[(kw, name, statement, start_line, end_line_of_statement)] with 1-based lines."""
    t = strip_comments(text)
    lines = t.split("\n")
    res = []
    for k, l in enumerate(lines):
        if l[:1].isspace() or not l.strip():
            continue
        h = HEAD.match(l)
        if not h:
            continue
        # scan from this line for the end of the statement
        depth, buf, end = 0, [], None
        for k2 in range(k, len(lines)):
            s = lines[k2]
            if k2 > k and s.lstrip().startswith("|") and depth == 0:
                end = k2; break
            i = 0
            while i < len(s):
                c = s[i]
                if c in "([{⟨":
                    depth += 1
                elif c in ")]}⟩":
                    depth -= 1
                elif depth == 0 and s.startswith(":=", i):
                    buf.append(s[:i]); end = k2; break
                elif depth == 0 and re.match(r"\bwhere\b", s[i:]) and (i == 0 or not (s[i - 1].isalnum() or s[i - 1] == "_")):
                    buf.append(s[:i]); end = k2; break
                i += 1
            if end is not None:
                break
            buf.append(s)
            if k2 > k + 200:
                break
        stmt = "\n".join(buf)
        name = h.group(2).split()[0] if h.group(2).split() else ""
        res.append((h.group(1), name, stmt, k + 1, (end if end is not None else k) + 1))
    return res


def strip_attr(text, attr):
    """remove `attr` from every @[...] list in text; drop lists that become empty"""
    def fix(mo):
        items = [x.strip() for x in mo.group(1).split(",") if x.strip() and x.strip() != attr]
        return ("@[" + ", ".join(items) + "]") if items else ""
    out = re.sub(r"@\[([^\]]*)\]", fix, text)
    return re.sub(r"^\s*\n", "", out)


def main():
    old_root, new_root, rem_f, hdr_f = sys.argv[1:5]
    allowed_rem = {l.strip() for l in open(rem_f) if l.strip()}
    rows = [l.rstrip("\n").split("\t") for l in open(hdr_f) if l.strip()]
    allowed_hdr = {(r[0], r[1]) for r in rows if r[0] != "ATTR"}
    allowed_attr = {(r[1], r[2]): r[3] for r in rows if r[0] == "ATTR"}
    # STMT rows: module, declaration whose statement text may change (class `statement text: Mathlib API rename`,
    # each one checked separately by the 4.32 pp.all identity test)
    allowed_stmt = {(r[1], r[2]) for r in rows if r[0] == "STMT"}
    mods = sys.argv[5:]
    if not mods:
        for dp, _, fs in os.walk(old_root):
            for f in fs:
                if f.endswith(".lean"):
                    mods.append(os.path.relpath(os.path.join(dp, f), old_root)[:-5].replace("/", "."))
    findings, checked = [], 0
    for m in sorted(mods):
        rel = m.replace(".", "/") + ".lean"
        po, pn = os.path.join(old_root, rel), os.path.join(new_root, rel)
        if not os.path.exists(pn):
            if m not in allowed_rem:
                findings.append((m, "removed", "module removed without an allowance", ""))
            continue
        a, b = open(po, encoding="utf-8").read(), open(pn, encoding="utf-8").read()
        if a == b:
            continue
        checked += 1
        da, db = decls(a), decls(b)
        def norm(x):
            if (m, x[1]) in allowed_stmt:
                return (x[0], x[1], "<statement edit allowed by STMT row>")
            at = allowed_attr.get((m, x[1]))
            return (x[0], x[1], strip_attr(x[2], at).strip() if at else x[2])
        sa = [norm(x) for x in da]
        sb = [norm(x) for x in db]
        if sa != sb:
            for x, y in zip(sa + [None] * (len(sb) - len(sa)), sb + [None] * (len(sa) - len(sb))):
                if x != y:
                    findings.append((m, "statement", f"old {x[:2] if x else None} new {y[:2] if y else None}",
                                     (x[2] if x else "")[-200:].replace("\n", "\\n") + " || " + (y[2] if y else "")[-200:].replace("\n", "\\n")))
                    break
        al, bl = a.split("\n"), b.split("\n")
        sm = difflib.SequenceMatcher(a=al, b=bl, autojunk=False)
        for tag, i1, i2, j1, j2 in sm.get_opcodes():
            if tag == "equal":
                continue
            # position in the OLD file of the change: lines i1..i2 (or the insertion point i1)
            touched = range(i1 + 1, max(i2, i1 + 1) + 1) if tag != "insert" else [i1 + 1]
            for ln in touched:
                enc = [d for d in da if d[3] <= ln]
                enc = enc[-1] if enc else None
                if enc is None:
                    for nl in bl[j1:j2]:
                        # attribute lines are judged by step 4
                        if re.match(r"^\s*(@\[|attribute\s*\[)", nl):
                            continue
                        if (m, nl) not in allowed_hdr:
                            findings.append((m, "header", f"old line {ln}", nl[:200]))
                    break
                # the statement's last line may also hold the start of the proof (`... := by`, one-line
                # instances): that line is covered by the exact statement comparison of step 1
                if (m, enc[1]) in allowed_stmt:
                    continue
                if tag != "insert" and ln < enc[4]:
                    findings.append((m, "before :=", f"{enc[0]} {enc[1]} old line {ln}", al[ln - 1][:200]))
                if tag == "insert" and ln <= enc[4] and ln > enc[3]:
                    findings.append((m, "before :=", f"{enc[0]} {enc[1]} insertion at old line {ln}", ""))
            # step 4: attribute lines
            ATT = re.compile(r"^\s*(@\[|attribute\s*\[)")
            olds, news = al[i1:i2], bl[j1:j2]
            for k, nl in enumerate(news):
                if not ATT.match(nl):
                    continue
                nxt = [d for d in db if d[3] >= j1 + k + 1]
                name = nxt[0][1] if nxt else ""
                at = allowed_attr.get((m, name))
                ok = False
                if at:
                    stripped = strip_attr(nl, at)
                    ok = (stripped.strip() == "" and tag == "insert") or (stripped in olds)
                if not ok:
                    findings.append((m, "attribute", f"new line {j1 + k + 1} (next declaration {name})", nl[:200]))
            def allowed_strip(k, nl):
                nxt = [d for d in db if d[3] >= j1 + k + 1]
                at = allowed_attr.get((m, nxt[0][1] if nxt else ""))
                return strip_attr(nl, at) if at else nl
            for ol in olds:
                if ATT.match(ol) and tag in ("delete", "replace") and not any(
                        allowed_strip(k, nl) == ol for k, nl in enumerate(news)):
                    findings.append((m, "attribute", "removed attribute line", ol[:200]))
            removed_text = "\n".join(al[i1:i2])
            for nl in bl[j1:j2]:
                for tok in ("sorry", "admit", "native_decide", "maxHeartbeats", "maxRecDepth", "set_option", "axiom", "decide"):
                    if re.search(r"(?<![\w.])" + tok + r"(?![\w])", nl) and not (tok == "decide" and "decide" in removed_text):
                        findings.append((m, "forbidden", tok, nl[:200]))
    for f in findings:
        print("\t".join(f))
    print(f"checked {checked} changed modules; findings {len(findings)}", file=sys.stderr)
    sys.exit(1 if findings else 0)


if __name__ == "__main__":
    main()
