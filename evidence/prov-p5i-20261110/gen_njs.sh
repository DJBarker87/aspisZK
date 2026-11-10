cd "$(dirname "$0")"
python3 -B PCWS_gen_equalities.py --module NJS_Extract.Funs \
 --fresh-dir inputs/fresh_E003p --fresh-ns PCWS_njs \
 --gate-source inputs/gate_NJS_Extract_Funs.lean --gate-types-source inputs/gate_NJS_Extract_Types.lean \
 --only inputs/only_njs.json --fresh-prelude inputs/njs_vars.lean --prune-fresh --tag=${1:-_s1} \
 --out PRVEq_NJS_Extract_Funs${1:-_s1}.lean --report gen/njs${1:-_s1}.report.json --state-out gen/njs${1:-_s1}.state.json 2>&1 | tail -25 | cut -c1-300
rm -rf __pycache__
