import re,csv,sys,collections
S=sys.argv[1]
mine=open('/Users/dominic/aspis-lead-infra/ONCHAIN-PATH-EXTRACTION-STATUS-20261111.md').read().splitlines()
rows=[]
for ln in mine:
    if not ln.startswith('| `'): continue
    m=re.match(r'\| `([^`]+)`',ln); name=m.group(1)
    tail=name.split('::')[-1].split('(')[0].strip()
    rows.append((name,tail,ln))
frozen=list(csv.DictReader(open(S+'/rows-frozen.tsv'),delimiter='\t'))
bytail=collections.defaultdict(list)
for r in frozen: bytail[r['function'].split('::')[-1]].append(r)
# rename map tails (old tail -> new tail) for fn rows
ren={}
for r in csv.DictReader(open(S+'/rename_map.tsv'),delimiter='\t'):
    if r['kind'].startswith('fn') and not r['new'].startswith('('):
        ren[r['old'].split('::')[-1]]=r['new'].split('::')[-1]
out=[];cnt=collections.Counter();unmatched=[]
seen=set()
for name,tail,ln in rows:
    t=ren.get(tail,tail)
    hits=bytail.get(t,[])
    if not hits: cnt['no frozen row']+=1; unmatched.append(name); continue
    cls=set((h['scope'],h['translates'][:12],h['elaborates'][:3],h['class'],h['pin_text']) for h in hits)
    for h in hits: seen.add(h['function'])
    k='|'.join(sorted(set(f"{c[3]}/{c[4]}/{c[2]}" for c in cls)))
    cnt[k]+=1
    out.append((name,k,';'.join(h['function'] for h in hits)))
print("my rows:",len(rows))
for k,v in cnt.most_common(): print(v,k)
print("\nunmatched (no frozen row), %d:"%len(unmatched)); print(', '.join(sorted(set(unmatched))))
new=[r for r in frozen if r['function'] not in seen]
print("\nfrozen rows not keyed by my table: %d"%len(new))
c2=collections.Counter((r['scope'],r['class']) for r in new)
for k,v in sorted(c2.items()): print(v,k)
print("\nAspis-only new gates (not in PIN2 table):")
for r in new:
    if 'Aspis-only' in r['class']: print(' ',r['scope'],r['function'])
with open(S+'/rekey_rows.tsv','w') as f:
    for o in out: f.write('\t'.join(o)+'\n')
