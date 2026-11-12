#!/usr/bin/env python3
"""X3: classify the closure modules of fv_x3_closure.py into kinds a-d and trace every kind (d) module.

Reads only.
  a  Aspis model chain module (source tag 'chain')
  b  vendored maths package over Mathlib only (source tag 'comppoly'; checked: no Aeneas import or mention)
  c  maths / bound-layer module of the earlier proof about a model (everything else not in d)
  d  R1 gate carrier. Seed: a generated module (last component Types, Funs, FunsExternal, TypesExternal, or a
     name of the families LIB_V*, LIBB_*, LIBC_*, RPz*, RPv*, RPu*, NDO*, NNH*, NNG*, NMX*), or a module that
     imports Aeneas directly. Then, to a fixpoint: a module that directly imports a (d) module AND whose text
     (comments removed) references a name declared in that module (word match on the last name component,
     at least 5 characters, and not a name Lean or Mathlib commonly declares, see COMMON).
Column reaches_d: 1 when the module's own import closure contains a (d) module.

Usage: fv_x3_kinds.py <closure.tsv> <out-modules.tsv> <out-d-report.tsv> <out-chain-paths.tsv>
"""
import collections, re, sys

FAMILY = re.compile(r"^(LIB_V|LIBB_|LIBC_|RPz|RPv|RPu|NDO|NNH|NNG|NMX)")
GEN_LAST = {"Types", "Funs", "FunsExternal", "TypesExternal"}
DECL = re.compile(r"^\s*(?:@\[[^\]]*\]\s*)*(?:(?:private|protected|noncomputable|partial|unsafe|nonrec)\s+)*"
                  r"(def|theorem|lemma|abbrev|structure|inductive|class|instance|opaque|axiom)\s+"
                  r"([A-Za-z_«][^\s:({\[]*)", re.M)
COMMON = {"State", "Bytes", "Byte", "decode", "encode", "length", "append", "valid", "Valid", "spec", "toList",
          "default", "instance", "value", "inner", "check", "Error"}


def strip(t):
    t = re.sub(r"/-.*?-/", " ", t, flags=re.S)
    return re.sub(r"--[^\n]*", "", t)


def main():
    cl, out_m, out_d, out_p = sys.argv[1:5]
    rows = {}
    order = []
    for i, line in enumerate(open(cl)):
        if i == 0:
            continue
        f = line.rstrip("\n").split("\t")
        m = f[0]
        order.append(m)
        rows[m] = dict(src=f[1], path=f[2], lines=int(f[3]), sha=f[4], ai=int(f[5]), am=int(f[6]),
                       ext=[x for x in f[7].split(",") if x], loc=[x for x in f[8].split(",") if x])
    text, decls = {}, {}
    for m, r in rows.items():
        t = strip(open(r["path"], encoding="utf-8", errors="replace").read()) if r["path"] else ""
        text[m] = t
        names = set()
        for _, n in DECL.findall(t):
            last = n.split(".")[-1].strip("«»")
            if len(last) >= 5 and last not in COMMON:
                names.add(last)
        decls[m] = names

    kind, why = {}, {}
    for m, r in rows.items():
        if r["src"] == "chain":
            kind[m] = "a"
        elif r["src"] == "comppoly":
            kind[m] = "b"
    for m, r in rows.items():
        if m in kind:
            continue
        last = m.split(".")[-1]
        if last in GEN_LAST or FAMILY.match(m) or FAMILY.match(m.split(".")[0]):
            kind[m] = "d"; why[m] = "generated module of the R1 extraction (name)"
        elif r["ai"]:
            kind[m] = "d"; why[m] = "imports Aeneas directly"
    uses = collections.defaultdict(dict)  # importer -> {d module: [names]}
    changed = True
    while changed:
        changed = False
        for m in order:
            if m in kind:
                continue
            for i in rows[m]["loc"]:
                if kind.get(i) != "d":
                    continue
                if rows[i]["src"] == "chain":
                    continue
                hit = sorted(n for n in decls[i] if re.search(r"(?<![\w.])(?:[\w.]*\.)?" + re.escape(n) + r"(?![\w])",
                                                              text[m]))
                gen = i.split(".")[-1] in GEN_LAST
                if hit or gen:
                    uses[m][i] = hit
            if uses[m]:
                kind[m] = "d"
                why[m] = "imports and references " + ";".join(
                    f"{i}[{','.join(v[:6])}{'...' if len(v) > 6 else ''}]" for i, v in uses[m].items())
                changed = True
    for m in order:
        kind.setdefault(m, "c")
    # chain modules and their uses of d modules too (should be none)
    for m in order:
        if kind[m] == "a":
            for i in rows[m]["loc"]:
                if kind.get(i) == "d":
                    uses[m][i] = sorted(n for n in decls[i] if re.search(r"\b" + re.escape(n) + r"\b", text[m]))

    # tier of a (d) module: generated | aeneas-import | translated-content (its text names a translated
    # namespace, a namespace of the 431/432 serializer-withdrawal-adapter refinement modules, or an Aeneas
    # slice/scalar type) | import-only (imports a d module; the names it uses from it are stated over model
    # objects only)
    content_re = re.compile(r"AspisR1AdapterReconstruct|AspisR1PublicSerializer|AspisR1WithdrawalValidation|"
                            r"Whole431|FieldsRefinement431|RawBridge431|StageBinding|SerializerWitness|"
                            r"PaymentGuard|SuppliedPublicBinding|\bU8\b|\bSlice\b")
    tier = {}
    for m in order:
        if kind[m] != "d":
            continue
        if why.get(m, "").startswith("generated"):
            tier[m] = "generated"
        elif why.get(m, "").startswith("imports Aeneas"):
            tier[m] = "aeneas-import"
        elif content_re.search(text[m]):
            tier[m] = "translated-content"
        else:
            tier[m] = "import-only"

    # import closure reachability of d
    reach = {}
    for m in order:  # order is dependency order
        reach[m] = any(kind[i] == "d" or reach.get(i, False) for i in rows[m]["loc"])

    importers = collections.defaultdict(list)
    for m in order:
        for i in rows[m]["loc"]:
            importers[i].append(m)

    with open(out_m, "w") as f:
        f.write("module\tkind\td_tier\tsource\tpath\tlines\tsha256\taeneas_import\taeneas_mention_count\treaches_d\t"
                "closure_imports\tkind_reason\n")
        for m in order:
            r = rows[m]
            f.write("\t".join([m, kind[m], tier.get(m, ""), r["src"], r["path"], str(r["lines"]), r["sha"], str(r["ai"]),
                               str(r["am"]), str(int(reach[m])), ",".join(r["loc"]), why.get(m, "")]) + "\n")

    # shortest path from each chain module through non-chain modules to each d module
    dset = [m for m in order if kind[m] == "d"]
    with open(out_d, "w") as f:
        f.write("d_module\td_tier\tlines\treason\timporters_in_closure\tnames_used_by_importers\n")
        for d in dset:
            used = {imp: uses[imp].get(d) for imp in importers[d] if d in uses.get(imp, {})}
            f.write("\t".join([d, tier[d], str(rows[d]["lines"]), why.get(d, ""), ",".join(importers[d]),
                               "; ".join(f"{k}:{','.join(v) if v else '(module import; generated)'}"
                                         for k, v in used.items())]) + "\n")
    with open(out_p, "w") as f:
        f.write("chain_module\tfirst_non_chain_import\td_modules_reached\tshortest_path_to_nearest_d\n")
        for c in order:
            if kind[c] != "a":
                continue
            for i in rows[c]["loc"]:
                if kind[i] == "a" or not (reach[i] or kind[i] == "d"):
                    continue
                # BFS from i to a d module
                prev, q, found = {i: None}, collections.deque([i]), None
                reached = set()
                while q:
                    x = q.popleft()
                    if kind[x] == "d":
                        reached.add(x)
                        if found is None:
                            found = x
                        continue
                    for y in rows[x]["loc"]:
                        if y not in prev:
                            prev[y] = x; q.append(y)
                path = []
                x = found
                while x is not None:
                    path.append(x); x = prev[x]
                f.write("\t".join([c, i, ",".join(sorted(reached)), " -> ".join([c] + path[::-1])]) + "\n")
    cnt = collections.Counter(kind.values())
    print(dict(cnt), dict(collections.Counter(tier.values())), "reaches_d:", sum(reach.values()), file=sys.stderr)


if __name__ == "__main__":
    main()
