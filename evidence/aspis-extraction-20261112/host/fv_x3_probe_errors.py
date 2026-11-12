#!/usr/bin/env python3
"""X3 stage B: classify the Lean errors of the raw-emission probe (reads the logs and the compiled sources).

One row per error message: scope, module, line, enclosing declaration, Lean error code, cause class, Rust path or
name, message (first 300 characters). Classes, by message text and the emitted line:
  1-absent        a library item the emission needs that the native library does not define
                  (Iterator methods zip/fold/any/rev as fields of the trait structure; ChunksExactMut)
  2-name-clash    a parameter or local named like a module (`compact`, `weights`) shadows the module in a
                  qualified name: "Invalid field ... from an expression compact/weights"
  3-ok_or-purity  `lift (core.option.Option.ok_or ..)`: the emitter treats Option::ok_or as pure, the native
                  library returns Result; surfaces at the next use (CoreOpsTry.branch)
  3-line-break    emitter line breaks at its indentation limit leave applications split over lines
  3-recdepth      maximum recursion depth on a large array literal
  3-mut-iter      mutable-iterator encoding: the emission destructures a backward function that the native
                  model of the adapter does not return (Zip over ChunksExactMut; ChunksExactMut::next)
  consequential   unknown constant that failed to elaborate earlier in the same file
Usage: fv_x3_probe_errors.py <probe-dir> <out.tsv>
"""
import re, sys

SCOPES = [("v", "AspisTPv"), ("p", "AspisTPp"), ("s", "AspisTP2g"), ("d", "AspisTP3stmt"), ("c", "AspisTP3core")]
DECL = re.compile(r"(?:@\[[^\]]*\]\s*)?(?:noncomputable |partial |private |divergent )*"
                  r"(def|theorem|abbrev|instance|structure|impl_def)\b\s*(\S*)")


def classify(msg, line_text, prev_text):
    if "is not a field of structure `core.iter.traits.iterator.Iterator`" in msg:
        f = re.search(r"`(\w+)` is not a field", msg).group(1)
        return "1-absent", f"core::iter::traits::iterator::Iterator::{f} (not a field of the native trait structure)"
    if "Unknown constant" in msg:
        return "consequential", re.search(r"`([^`]+)`", msg).group(1)
    m = re.search(r"Invalid field `(\w+)`.*from an expression (\w+) of type", msg)
    if m and m.group(2) in ("compact", "weights"):
        return "2-name-clash", f"local `{m.group(2)}` shadows module {m.group(2)} ({m.group(1)})"
    if "CoreOpsTry.branch" in msg and "ok_or" in prev_text:
        return "3-ok_or-purity", "core::option::Option::ok_or"
    if "maximum recursion depth" in msg:
        return "3-recdepth", "512-entry array literal"
    if "expected a product type, got core.iter.adapters.zip.Zip" in msg:
        return "3-mut-iter", "core::iter::adapters::zip::Zip<ChunksExact, ChunksExactMut>::next"
    if "ChunksExactMut.Insts.CoreIterTraitsIteratorIteratorMutASlice.next has type" in msg:
        return "3-mut-iter", "core::slice::iter::ChunksExactMut::next (template signature with backward function)"
    return "3-line-break", "applications split by the emitter's line breaks"


def main():
    d, out = sys.argv[1], sys.argv[2]
    rows = []
    for s, ns in SCOPES:
        src = open(f"{d}/{s}/src/{ns}/Funs.lean").read().split("\n")
        log = open(f"{d}/{s}/Funs.log").read()
        for part in re.split(r"(?m)^(?=\S+\.lean:\d+:\d+: (?:error|warning))", log):
            m = re.match(r"\S+\.lean:(\d+):\d+: error(\([\w.]+\))?: ?(.*)", part, re.S)
            if not m:
                continue
            ln = int(m.group(1)); msg = " ".join(m.group(3).split())
            dec = "?"
            for k in range(ln - 1, -1, -1):
                t = DECL.match(src[k])
                if t:
                    dec = t.group(2) or src[k + 1].strip()
                    break
            prev = "\n".join(src[max(0, ln - 4):ln])
            cls, name = classify(msg, src[ln - 1], prev)
            rows.append((s, f"{ns}.Funs", str(ln), dec, (m.group(2) or "").strip("()"), cls, name, msg[:300]))
    with open(out, "w") as f:
        f.write("scope\tmodule\tline\tdeclaration\tlean_code\tcause_class\trust_path_or_name\tmessage\n")
        for r in rows:
            f.write("\t".join(r) + "\n")
    import collections
    c = collections.Counter((r[0], r[5]) for r in rows)
    for k in sorted(c):
        print(*k, c[k])


if __name__ == "__main__":
    main()
