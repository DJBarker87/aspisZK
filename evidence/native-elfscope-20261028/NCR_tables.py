import pathlib,json,collections
E=pathlib.Path(__file__).parent
s=json.loads((E/'NCR_RECEIPT_SAMPLE.json').read_text());scan=json.loads((E/'NCR_BODY_SCAN.json').read_text())
p=E/'NCR_FEATURE_TABLE.md';base=p.read_text().split('<!-- GENERATED -->')[0]
text=['<!-- GENERATED -->','| Reached body | Conditional/assertion lines |','|---|---|']
seen=set()
for h in scan['hits']:
 k=(h['file'],h['start'])
 if k in seen:continue
 seen.add(k)
 hits=[str(x['line'])+': '+x['text'].strip() for x in h['hits'] if any(v in x['text'] for v in ['cfg','debug_assert'])]
 if hits:text.append('| `'+h['file']+'::'+h['name']+'@'+str(h['start'])+'` | '+ '<br>'.join(x.replace('|','&#124;') for x in hits)+' |')
text+=['','## Representative receipt lanes','',f'{len(s)} sampled receipts across {len(set(x["path"].split("/")[1] for x in s))} lanes. These include failures/negative controls; sampling is configuration evidence, not proof credit. Full commands/environments/source pins/statuses are retained in [NCR_RECEIPT_SAMPLE.json](NCR_RECEIPT_SAMPLE.json); wrapper source in [NCR_WRAPPERS.json](NCR_WRAPPERS.json).','', '| Lane / first sampled receipt | Effective command class / features | Profile/flags |','|---|---|---|']
for lane,xs in sorted(collections.defaultdict(list, {lane:[x for x in s if x['path'].split('/')[1]==lane] for lane in {x['path'].split('/')[1] for x in s}}).items()):
 x=xs[0];j=x['receipt'];c=x['effective_command'];env=j.get('env',{});features=c[c.index('--features')+1] if '--features' in c else 'no explicit features';root=c[c.index('--manifest-path')+1].split('/src/')[-1] if '--manifest-path' in c else ('standalone '+c[1] if c and c[0].endswith('kani-driver') else 'wrapper; see snapshot')
 if lane=='native-tx1top-20261028':root='programs/r1-cost-probe (NCL_gate.py)';features='pool-adapter,private-leaf-salts'
 profile='release' if '--release' in c else ('standalone profile unspecified' if c and c[0].endswith('kani-driver') else 'dev; opt='+str(env.get('CARGO_PROFILE_DEV_OPT_LEVEL','unspecified')))
 flags=env.get('RUSTFLAGS','unrecorded')
 text.append('| `'+lane+'` / `'+x['path'].split('/')[-2]+'` | `'+root+'`; '+features+' | '+profile+'; `'+flags+'` |')
p.write_text(base+'\n'.join(text)+'\n')
