import json,re,sys,glob
STD={'propext','Classical.choice','Quot.sound'}
for a in sys.argv[1:]:
    r=json.load(open(f'PCQI_{a}/receipt.json'));bad=[];n=0
    for x in r['print_axioms']:
        x=re.sub(r'\s+',' ',x);m=re.match(r"'([^']+)' (?:depends on axioms: \[(.*)\]|does not depend on any axioms)",x);n+=1
        ax={s.strip() for s in (m.group(2) or '').split(',') if s.strip()}
        if ax-STD:bad.append((m.group(1),ax-STD))
    print(a,'exit',r['exit_status'],'theorems',n,'nonstandard',bad)
