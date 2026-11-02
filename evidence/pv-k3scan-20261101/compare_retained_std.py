"""Conservative exact-origin/instantiation comparison; unresolved entries stay withheld."""
from pathlib import Path
import json,lzma,subprocess,hashlib,re
E=Path(__file__).resolve().parent;R='4bc59099b98552f79d92d2a2ce289dab3faedbaa';out=E/'retained-std';out.mkdir(exist_ok=True)
def load_old(group):
 base='evidence/pv-b3p6-20261028/resume17/host-recovery/std-'+group+'/'
 b=subprocess.check_output(['git','show',R+':'+base+'index.json']);(out/(group+'-index.json')).write_bytes(b);idx=json.loads(b);v=idx['records'][0];name=Path(v['symbol_dump']).name;raw=subprocess.check_output(['git','show',R+':'+base+name]);assert hashlib.sha256(raw).hexdigest()==v['symbol_dump_sha256'];(out/(group+'-'+name)).write_bytes(raw)
 return next(x['symbolTable']for x in json.loads(lzma.decompress(raw))if 'symbolTable'in x),v

def items(tab):
 out=[]
 for k,v in tab.items():
  if v.get('type',{}).get('id')!='code':continue
  loc=v.get('location',{});p=loc.get('file','')
  if '/rust/library/' not in p and not re.search(r'/rustc/.*?/library/(?:std|alloc|core)/',p):continue
  rel=p.split('/rust/library/')[-1] if '/rust/library/'in p else p.split('/library/')[-1]
  out.append({'name':v.get('prettyName',k),'type':v.get('prettyType'),'file':rel,'function':loc.get('function'),'line':loc.get('line')})
 return out
records=[]
for ident,group in [('K79209','reconstruct'),('K79211','transition')]:
 old,v=load_old(group);index=json.loads((E/'host'/ident/'symbols-index.json').read_text());entry=index['records'][0];raw=lzma.decompress((E/'host'/ident/entry['symbols']).read_bytes());assert hashlib.sha256(raw).hexdigest()==entry['symbols_raw_sha256'];tab=next(x['symbolTable']for x in json.loads(raw)if 'symbolTable'in x)
 before=items(old);new=items(tab);strict=lambda x:tuple(x[k]for k in ['name','type','file','function','line']);keys={strict(x)for x in before};unresolved=[x for x in new if strict(x)not in keys]
 records.append({'id':ident,'group':group,'old_record':v,'new_std_entries':new,'old_std_count':len(before),'exact_origin_instantiation_matches':len(new)-len(unresolved),'unresolved':unresolved,'decision':'No blanket transfer. Exact matching entries reuse their historical source-token/per-item argument evidence; nonmatching type/name/source mappings require review. Intrinsics remain V370. This is not a fresh per-item body parity proof.'})
(E/'D549-STD-COMPARISON.json').write_text(json.dumps({'records':records,'scope':'Exact reached-code inventory comparison to previously retained historical std evidence; not a compiler theorem or an automatic deployed release.'},indent=2)+'\n');print([(r['id'],len(r['new_std_entries']),r['exact_origin_instantiation_matches'],len(r['unresolved']))for r in records])
