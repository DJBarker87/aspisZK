import json,re,subprocess,collections
F='4bb3b3f51e16b4525f1d10336e2b0bcbbd775387'
R='../../'
h=json.load(open('PCQK_FIRST_HALF.json'))
txt=subprocess.run(['git','-C',R,'grep','-h','-E',r'(fn|struct|enum|const|static|type|trait) +[A-Za-z_0-9]+',F,'--','crates','programs/r1-cost-probe'],capture_output=True,text=True).stdout
names=set(re.findall(r'(?:fn|struct|enum|const|static|type|trait) +([A-Za-z_0-9]+)',txt))
out=[];c=collections.Counter()
for x in h:
    d=x['definition']
    parts=[p for p in re.split(r'[.]',d)]
    # drop leading namespace token
    ids=[p for p in parts[1:] if p and not re.match(r'^(closure(_\d+)?|body|Insts|match_\d+|splitter)$',p) and not p.startswith(('CoreOps','CoreCmp','CoreClone','CoreMarker','CoreDefault'))]
    key=ids[-1] if ids else parts[-1]
    key2=re.sub(r'_loop\d*(_loop\d+)?$','',key)
    hit=key in names or key2 in names
    x2=dict(module=x['module'],definition=d,key=key2,frozen_name_present=hit,rows=x['rows'])
    out.append(x2);c[hit]+=1
json.dump(out,open('PCQK_NAMECHECK.json','w'),indent=0)
print(c)
print(sorted({o['key'] for o in out if not o['frozen_name_present']})[:80])
