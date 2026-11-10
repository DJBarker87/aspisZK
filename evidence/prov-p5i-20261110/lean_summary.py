import json,lzma,re,sys
a=sys.argv[1]
r=json.load(open(a+'/receipt.json')); print(r['exit_status'],round(r['wall_seconds'],1),r['peak_rss_kib'],r['swaps'])
log=lzma.open(a+'/stdout.log.xz','rt').read()
ls=[l for l in log.splitlines() if re.search(r'error',l,re.I) and 'sources/' in l]
print('errors',len(ls))
for l in ls[:int(sys.argv[2]) if len(sys.argv)>2 else 20]: print(l[:230].replace('PCWS_sources/',''))
ax=[l for l in log.splitlines() if 'depends on axioms' in l or 'does not depend' in l]
import itertools
txt=re.sub(r'\n\s+',' ',log)
bad=[m for m in re.findall(r"'[^']+' depends on axioms: \[([^\]]*)\]",txt) if any(t.strip() not in ('propext','Classical.choice','Quot.sound') for t in m.split(','))]
print('axioms lines',len(re.findall(r"depends on axioms|does not depend",txt)),'nonstandard',len(bad),bad[:2])
