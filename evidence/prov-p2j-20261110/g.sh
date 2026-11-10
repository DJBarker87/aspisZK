cd "$(dirname "$0")"
for d in batch_keys_loop.body sort_batch_keys_loop0.body sort_batch_keys_loop0_loop0.body; do echo "== $d"; awk "/^def verifier.candidate.$d/{f=1} f{print} /^$/{if(f)exit}" inputs/gate_NJS_Extract_Funs.lean | grep -n 'wrapping\|<<<\| - \| + ' | head -6; done
echo == fresh ON; grep -n 'sort_batch_keys_loop0_loop0.body' -A14 PCUJ_E003_emitted/raw/NJS_Extract/Funs.lean | grep -n '\- \|+ ' | head
