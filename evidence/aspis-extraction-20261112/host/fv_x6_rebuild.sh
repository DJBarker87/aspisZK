#!/bin/bash
# X6: rebuild the carried library and the Aspis model chain from a repository checkout under Lean 4.36.0-rc2,
# from scratch, one module at a time, in dependency order read from the files' import lines.
# Runs INSIDE one fv_slot.sh scope:
#   bash W/fv_slot.sh X6-rebuild-<n> <timeout> bash fv_x6_rebuild.sh <lib-dir> <chain-dir> <outdir> [root-module]
#   <lib-dir>   docs/research/future-version/lean-lib   (the ported carried library)
#   <chain-dir> docs/research/future-version/lean       (the Aspis chain; only the closure of root-module is built)
#   <outdir>    fresh directory: objects in <outdir>/obj, per-module log/time in <outdir>/log, result.tsv
#   root-module default AspisFailureBoundModel
# LEAN_PATH: <outdir>/obj, then the stage A objects of the native library (W/x3/aeneas-src/backends/lean/.lake:
# Aeneas, Mathlib and the other packages of its manifest). Nothing else.
set -u
W=/home/dombarker/project-offloads/future-version-20261111
B=$W/x3/aeneas-src/backends/lean
TCD=$HOME/.elan/toolchains/leanprover--lean4---v4.36.0-rc2
LIB=$1; CH=$2; O=$3; ROOT=${4:-AspisFailureBoundModel}
mkdir -p $O/obj $O/log
LP=$O/obj:$B/.lake/build/lib/lean; for p in $B/.lake/packages/*; do LP=$LP:$p/.lake/build/lib/lean; done
echo "LEAN_PATH=$LP" > $O/env.txt; $TCD/bin/lean --version >> $O/env.txt
python3 -I - $LIB $CH $ROOT > $O/order.tsv <<'EOF'
import os, sys
lib, ch, root = sys.argv[1:4]
src = {}
for base in (lib, ch):
    for dp, _, fs in os.walk(base):
        for f in fs:
            if f.endswith(".lean"):
                rel = os.path.relpath(os.path.join(dp, f), base)
                m = rel[:-5].replace("/", ".")
                if base == ch and "/" in rel:
                    continue
                assert m not in src, ("duplicate module", m)
                src[m] = (base, os.path.join(dp, f))
def imports(p):
    out = []
    for l in open(p, encoding="utf-8"):
        t = l.split()
        if not t: continue
        if t[0] == "import" or (len(t) > 1 and t[0] in ("public", "meta") and "import" in t[:3]):
            out.append(t[-1])
    return out
imp = {m: [i for i in imports(p) if i in src] for m, (_, p) in src.items()}
seen, order = set(), []
sys.setrecursionlimit(100000)
def visit(m):
    if m in seen: return
    seen.add(m)
    for i in imp[m]: visit(i)
    order.append(m)
visit(root)
for m in order:
    print(m, src[m][0], src[m][1], ",".join(imp[m]) or "-", sep="\t")
EOF
: > $O/result.tsv; mkdir -p $O/ok; n=0
while IFS=$'\t' read -r m root path imps; do
  n=$((n+1)); echo "$n $m" > $O/PROGRESS
  skip=""
  if [ "$imps" != "-" ]; then for i in ${imps//,/ }; do [ -f $O/ok/$i ] || { skip=$i; break; }; done; fi
  if [ -n "$skip" ]; then printf '%s\tskipped\t\t\t\t%s\n' "$m" "$skip" >> $O/result.tsv; continue; fi
  rel=${m//.//}; mkdir -p $O/obj/$(dirname $rel)
  s=$(date +%s.%N)
  /usr/bin/time -v -o $O/log/$m.time env PATH=/usr/bin:/bin LEAN_PATH=$LP timeout 900 $TCD/bin/lean -j1 -M7000 \
    -DElab.async=false -R $root -o $O/obj/$rel.olean -i $O/obj/$rel.ilean $path > $O/log/$m.log 2>&1
  rc=$?; e=$(date +%s.%N)
  [ $rc -eq 0 ] && : > $O/ok/$m
  printf '%s\t%s\t%s\t%s\t%s\t%s\n' "$m" "$rc" "$(python3 -c "print(round($e-$s,2))")" \
    "$(grep 'Maximum resident' $O/log/$m.time | awk '{print $NF}')" "$(grep -c ': error' $O/log/$m.log)" \
    "$(grep -m1 ': error' $O/log/$m.log | tr '\t' ' ' | cut -c1-300)" >> $O/result.tsv
done < $O/order.tsv
echo "done $n" > $O/PROGRESS
