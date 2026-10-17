from pathlib import Path
import json,hashlib,importlib.util,re,shutil
W=Path('/home/dombarker/project-offloads/aspis-r1-worker-c-verify-prefix-proof-20261017');spec=importlib.util.spec_from_file_location('r',W/'runner.py');r=importlib.util.module_from_spec(spec);spec.loader.exec_module(r);sha=lambda b:hashlib.sha256(b).hexdigest();ext=W/'external-inputs.json';d=json.loads(ext.read_text());m=json.loads((W/'sources/SOURCE-MANIFEST.json').read_text());backup=W/'checkpoint-binding-original';backup.mkdir(exist_ok=True);shutil.copy2(ext,backup/'external-inputs.json');shutil.copy2(W/'sources/SOURCE-MANIFEST.json',backup/'SOURCE-MANIFEST.json')
rev={n for n in d['modules'] if n.startswith('AspisR1PublicSerializer.')}
while True:
 extra={n for n,v in d['modules'].items() if set(v['imports'])&rev}-rev
 if not extra:break
 rev|=extra
assert len(rev)==13
orig={};repls=[];record=[]
for n in rev:
 p=Path(d['modules'][n]['source']);raw=p.read_bytes();orig[n]=raw
 if n=='AspisR1PublicSerializer.Types':
  s=raw.decode();errors=[('Allocation',0),('RowOrder',2),('InvalidRow',0),('Tag',1),('Length',1),('NonCanonical',2),('Boundary',1),('Terminal',0),('EqualCirclePoints',0),('TrailingBytes',0),('Public',0)];items=[('aspis_core.state_only_prefix.r0.Error',errors),('pool_v1.pair_forest_semantic_terminal.CompiledVariant',[('PrivateTransfer',0),('Withdrawal',0)]),('pool_v1.pair_forest_semantic_terminal.r0.Public',[('Transfer',2),('Withdrawal',2)])]
  for name,ctors in items:
   marker='@[discriminant isize]\ninductive '+name;assert s.count(marker)==1;start=s.index(marker);end=s.index('\n\n',start);body=s[start:end];assert re.findall(r'^\| (\w+)',body,re.M)==[c for c,_ in ctors]
   aux='\n\n-- Naming-only expansion; pinned Aeneas constructor codes retained.\ndef '+name+'.read_discriminant (x : '+name+') : Isize :=\n  match x with\n'+''.join('  | .'+c+' _'*arity+' => '+str(i)+'#isize\n' for i,(c,arity) in enumerate(ctors))+'\ninstance _root_.AspisR1PublicSerializer.'+name+'.instDiscriminant :\n    Aeneas.Std.Discriminant '+name+' Isize where\n  read_discriminant := '+name+'.read_discriminant'
   new=body.removeprefix('@[discriminant isize]\n')+aux;s=s.replace(body,new,1);repls.append((body,new));record.append({'type':name,'constructor_arities':ctors,'codes':[[c,i] for i,(c,_) in enumerate(ctors)],'before_sha256':sha(body.encode()),'after_sha256':sha(new.encode())})
  inverse=s
  for a,b in reversed(repls):assert inverse.count(b)==1;inverse=inverse.replace(b,a,1)
  assert inverse==raw.decode() and '@[discriminant isize]' not in s
  s=s.replace('\nend AspisR1PublicSerializer','\n'+''.join('#print axioms '+n+'.read_discriminant\n' for n,_ in items)+'end AspisR1PublicSerializer');raw=s.encode()
 p=W/'sources'/(r.stem(n)+'.lean');p.parent.mkdir(parents=True,exist_ok=True);p.write_bytes(raw)
 m['modules'][n]={'stage_as':r.stem(n)+'.lean','source_sha256':sha(raw),'imports':r.imports(p),'source_revision':'accepted serializer; naming-only joint import repair at current canonicala2b','source':str(Path(d['modules'][n]['source'])),'role':'Names-only serializer discriminant repair; complete exact reverse import refresh','axiom_requests':len(re.findall(r'^#print axioms ',raw.decode(),re.M))}
# Exact complete reverse importer set removed from cache; no nominal mixture.
for n in rev:del d['modules'][n]
for n in m['modules']:
 for dep in m['modules'][n]['imports']:assert dep in m['modules'] or dep in d['modules'],(n,dep)
order=[];seen=set()
def visit(n):
 if n in seen:return
 for dep in m['modules'][n]['imports']:
  if dep in m['modules']:visit(dep)
 seen.add(n);order.append(n)
for n in list(m['topological_order'])+sorted(rev):visit(n)
m['topological_order']=order;r.dump(W/'sources/SOURCE-MANIFEST.json',m);r.dump(ext,d)
r.dump(W/'serializer-naming-audit.json',{'original_source_sha256':sha(orig['AspisR1PublicSerializer.Types']),'adapted_source_sha256':r.sha(W/'sources/AspisR1PublicSerializer/Types.lean'),'instances':record,'inverse_recovers_original_bytes_before_audit_commands':True,'additional_audit_commands':3,'reverse_importer_set':sorted(rev),'source_equality':{n:{'old_sha256':sha(b),'staged_sha256':r.sha(W/'sources'/(r.stem(n)+'.lean')),'unchanged':n!='AspisR1PublicSerializer.Types'} for n,b in orig.items()},'rule':'Exact pinned Aeneas discriminant macro expansion with fully qualified instance identity. Every constructor, arity and numerical code retained. All13 reverse importers rebuilt from source, no old object mixed.'})
print('STAGED names-only repair',len(rev),'modules; no compiler')
