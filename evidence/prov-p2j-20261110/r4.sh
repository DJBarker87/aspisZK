cd "$(dirname "$0")"
python3 - <<'P'
import json,re
for a in ['L015','L016']:
    r=json.load(open(f'PCUJ_{a}/receipt.json'));print(a,r['exit_status'])
    for x in r['print_axioms']:
        x=re.sub(r'\s+',' ',x);print('   ',x[:150])
P
xz -dc PCUJ_L015/stdout.log.xz | grep -B2 -A25 ' error' | head -70 | cut -c1-220
