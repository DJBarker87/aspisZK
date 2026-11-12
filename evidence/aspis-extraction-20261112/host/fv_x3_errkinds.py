#!/usr/bin/env python3
"""X3: classify the Lean errors of a closure compile (fv_x3_closure_compile.sh output). Reads only.

Every error message of every failed module is classified by its text and the source line it points at:
  renamed-or-removed-name  unknown identifier / constant / namespace, or an unknown field (a Lean or Mathlib name
                           that no longer exists under that name)
  simp-behaviour           `simp` made no progress or failed, or unsolved goals at a line that runs simp/simp_all/
                           norm_num/field_simp
  rewrite-behaviour        rw/unfold failures: motive is not type correct, did not find instance of the pattern,
                           failed to rewrite using equation theorems
  tactic-behaviour         other tactic failures: omega, linarith, decide, positivity, nlinarith, ring, grind,
                           exact?/apply mismatch inside a tactic block, unsolved goals elsewhere
  syntax-or-parse          unexpected token, unknown tactic, unknown attribute, parse errors
  type-or-elaboration      type mismatch, application type mismatch, failed to synthesize, invalid field notation
  resource                 maximum recursion depth, heartbeats, deep recursion, timeouts
  other                    anything else
Usage: fv_x3_errkinds.py <compile-dir> <table.tsv> <out.tsv> <out-kinds.tsv>
  <compile-dir> holds result.tsv and log/<module>.log; <table.tsv> gives kind and lines per module.
Writes one row per module (out.tsv) and one row per error kind with its count and one example (out-kinds.tsv).
"""
import collections, re, sys

SIMP = re.compile(r"\b(simp|simp_all|simp_arith|norm_num|field_simp|dsimp|simpa|push_cast)\b")


def classify(msg, src_line):
    m = msg
    if re.search(r"maximum recursion depth|heartbeats|deep recursion|timeout", m):
        return "resource"
    if re.search(r"Unknown (identifier|constant)|unknown (identifier|constant|namespace)|unknown declaration|"
                 r"does not contain|Invalid field|invalid field|is not a field", m):
        return "renamed-or-removed-name"
    if re.search(r"unexpected token|unknown tactic|unknown attribute|expected term|expected command|"
                 r"unexpected identifier|unknown syntax|parse", m):
        return "syntax-or-parse"
    if re.search(r"simp made no progress|simp failed|simp_all made no progress|norm_num failed|"
                 r"linter.unusedSimpArgs|dsimp made no progress", m):
        return "simp-behaviour"
    if re.search(r"motive is not type correct|did not find instance of the pattern|"
                 r"Failed to rewrite|failed to rewrite|rewrite failed|unfold failed|"
                 r"Tactic `rewrite` failed|Tactic `unfold` failed", m):
        return "rewrite-behaviour"
    if m.startswith("unsolved goals"):
        return "simp-behaviour" if SIMP.search(src_line) else "tactic-behaviour"
    if re.search(r"omega|linarith|decide|positivity|nlinarith|ring|grind|aesop|exact\?|"
                 r"The rfl tactic|Tactic `\w+` failed|tactic '[\w.]+' failed|no goals|"
                 r"not a definitional|failed to prove|Not a definitional", m):
        return "tactic-behaviour"
    if re.search(r"[Tt]ype mismatch|failed to synthesize|application type mismatch|"
                 r"function expected|cannot be|Invalid", m):
        return "type-or-elaboration"
    return "other"


def main():
    d, table, out, outk = sys.argv[1:5]
    meta = {}
    rows = [l.rstrip("\n").split("\t") for l in open(table)]
    h = rows[0]
    for r in rows[1:]:
        x = dict(zip(h, r)); meta[x["module"]] = x
    res = [l.rstrip("\n").split("\t") for l in open(f"{d}/result.tsv")]
    kinds = collections.Counter(); example = {}; mods_by_kind = collections.Counter()
    with open(out, "w") as f:
        f.write("module\tkind\tlines\texit\twall_s\tpeak_rss_kb\terrors\tfirst_error_kind\tfirst_error_or_skip_reason\n")
        for r in res:
            r += [""] * (6 - len(r))
            m, ex = r[0], r[1]
            k = meta.get(m, {}).get("kind", ""); ln = meta.get(m, {}).get("lines", "")
            first_kind = ""
            if ex not in ("0", "skipped"):
                log = open(f"{d}/log/{m}.log", encoding="utf-8", errors="replace").read()
                srcp = meta.get(m, {}).get("path", "")
                try:
                    src = open(srcp, encoding="utf-8", errors="replace").read().split("\n")
                except OSError:
                    src = []
                seen = set()
                for part in re.split(r"(?m)^(?=\S+\.lean:\d+:\d+: (?:error|warning))", log):
                    mm = re.match(r"\S+\.lean:(\d+):\d+: error(\([\w.]+\))?: ?(.*)", part, re.S)
                    if not mm:
                        continue
                    ln_no = int(mm.group(1)); msg = " ".join(mm.group(3).split())
                    msg = re.split(r" '[^']+' depends on axioms", msg)[0]  # drop #print axioms output
                    cls = classify(msg, src[ln_no - 1] if 0 < ln_no <= len(src) else "")
                    kinds[cls] += 1
                    if cls not in seen:
                        mods_by_kind[cls] += 1; seen.add(cls)
                    example.setdefault(cls, f"{m}:{ln_no}: {msg[:300]}")
                    if not first_kind:
                        first_kind = cls
                if not first_kind:
                    first_kind = "no error line (exit %s)" % ex
                    kinds[first_kind] += 1; example.setdefault(first_kind, m)
            f.write("\t".join([m, k, ln, ex, r[2], r[3], r[4], first_kind, r[5]]) + "\n")
    with open(outk, "w") as f:
        f.write("error_kind\terror_sites\tmodules_with_this_kind\texample\n")
        for k, c in kinds.most_common():
            f.write(f"{k}\t{c}\t{mods_by_kind[k]}\t{example[k]}\n")
    st = collections.Counter(r[1] if r[1] in ("0", "skipped") else "failed" for r in res)
    print(dict(st), dict(kinds), file=sys.stderr)


if __name__ == "__main__":
    main()
