cd "$(dirname "$0")"
for e in E009 E010; do echo "== $e"; ls PCUJ_${e}_emitted/raw/; grep -o '^def [a-zA-Z_0-9.]*' PCUJ_${e}_emitted/raw/*/Funs.lean | grep 'pair_terminal\|pair_tree_profile\|field.P' | head -30; done
