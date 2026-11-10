cd "$(dirname "$0")"
python3 - <<'P'
import json,re
for a in ['L012','L013','L014']:
    r=json.load(open(f'PCUJ_{a}/receipt.json'))
    print(a,r['exit_status'])
    for x in r['print_axioms']:
        x=re.sub(r'\s+',' ',x); n=re.match(r"'PRVEq\.([^']+)'",x).group(1); print('   ',n[-90:],'SORRY' if 'sorryAx' in x else 'std')
P
for a in L012 L014; do echo "== $a"; xz -dc PCUJ_$a/stdout.log.xz | grep -A8 ' error' | head -60 | cut -c1-220; done
