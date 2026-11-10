import json,sys,re
r=json.load(open(sys.argv[1]+'/receipt.json'))
std={'propext','Classical.choice','Quot.sound'}
bad=[];n=0
for x in r['print_axioms']:
    n+=1
    if 'does not depend' in x: continue
    m=re.search(r'axioms: \[(.*)\]',x,re.S)
    a={y.strip() for y in m.group(1).split(',')} if m else {'?'}
    if not a<=std: bad.append(x[:200])
print(sys.argv[1],'exit',r['exit_status'],'wall',round(r['wall_seconds'],1),'rssGiB',round(int(r['peak_rss_kib'])/1048576,2),'swap',r['swaps'],'n_axioms',n,'nonstandard',bad)
