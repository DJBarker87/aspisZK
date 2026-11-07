from pathlib import Path
import re,subprocess,json,hashlib
E=Path(__file__).resolve().parent;rev='4bb3b3f51e16b4525f1d10336e2b0bcbbd775387';defs={}
for p in subprocess.check_output(['git','ls-tree','-r','--name-only',rev,'crates/aspis-statement/src/pool_v1'],text=True).splitlines():
 if not p.endswith('.rs'):continue
 raw=subprocess.check_output(['git','show',rev+':'+p],text=True)
 for m in re.finditer(r'pub enum (\w+)\s*\{([^}]+)\}',raw,re.S):
  body=re.sub(r'//[^\n]*','',m[2]);variants=[]
  for line in body.splitlines():
   line=line.strip().rstrip(',')
   if not line:continue
   q=re.fullmatch(r'(\w+)(?:\(([^)]+)\))?(?:\s*=\s*[^,]+)?',line)
   if q:variants.append((q[1],q[2]))
   else:variants=[];break
  if variants:defs[m[1]]=(p,variants)
out=[];used={}
def make(t):
 t=t.strip()
 if t in ['u8','u16','u32','u64','usize']:return 'kani::any()'
 if t in used:return 'NMN_any_'+t+'()'
 assert t in defs,t
 p,vs=defs[t];used[t]={'path':p,'variants':vs}
 full='aspis_statement::pool_v1::'+Path(p).stem+'::'+t
 arms=[]
 for i,(v,arg) in enumerate(vs):arms.append(str(i)+'=>'+full+'::'+v+('('+','.join(make(a) for a in arg.split(','))+')' if arg else ''))
 arms[-1]='_=>'+arms[-1].split('=>',1)[1]
 out.append('fn NMN_any_'+t+'()->'+full+'{let t:u8=kani::any();kani::assume(t<'+str(len(vs))+');match t{'+','.join(arms)+'}}')
 return 'NMN_any_'+t+'()'
make('PoolV1PairForestTerminalFormatErrorV1')
(E/'NMN_format.rs').write_text('\n'.join(out)+'\n');(E/'NMN_FORMAT_ENUMS.json').write_text(json.dumps({'frozen_revision':rev,'types':used,'all_variants':True},indent=1)+'\n');print(json.dumps({'enum_types':len(used),'variants':sum(len(x['variants']) for x in used.values())}))
