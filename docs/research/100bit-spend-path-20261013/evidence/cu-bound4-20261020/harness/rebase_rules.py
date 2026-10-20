"""Rebase address rules only across equal named functions with equal masked instructions.
Pool .text unchanged: Pool rules retained exactly. Never guess an unmatched address.
Usage: rebase_rules.py old-verifier-link new-verifier-link old-rules out-rules mapping
"""
import sys,json,re,bisect
import sbf_slack as S
old,new,rules,out,mapping=sys.argv[1:]
def load(p):
 b=open(p,'rb').read();ss=S.elf_sections(b);t=next(s for s in ss if s['name']=='.text');fs=sorted((v,z,n) for v,z,n in S.elf_functions(b,ss) if t['addr']<=v<t['addr']+t['size']);return b[t['offset']:t['offset']+t['size']],t['addr'],fs
def base(n):return re.sub(r'17h[0-9a-f]{16}E$','',n)
def mask(t,a,v,z):
 b=bytearray(t[v-a:v-a+z]);i=0
 while i<len(b):
  if b[i] in (0x85,0x18):
   b[i+4:i+8]=bytes(4)
   if b[i]==0x18 and i+16<=len(b):b[i+12:i+16]=bytes(4);i+=8
  i+=8
 return bytes(b)
ot,oa,of=load(old);nt,na,nf=load(new);starts=[v for v,z,n in of];by={}
for v,z,n in nf:by.setdefault((base(n),z),[]).append(v)
mp={}
def addr(a):
 if a in mp:return mp[a].get('new')
 x=int(a,16);i=bisect.bisect_right(starts,x)-1
 if i<0:return None
 v,z,n=of[i];c=[nv for nv in by.get((base(n),z),[]) if mask(ot,oa,v,z)==mask(nt,na,nv,z)]
 mp[a]=dict(old_function=n,new=hex(c[0]+x-v) if len(c)==1 else None,matched_functions=len(c))
 return mp[a]['new']
r=json.load(open(rules))
for key in ['exclusions','loop_caps','callee_caps']:
 rr=[]
 for entry in r[key]:
  e=dict(entry)
  e['citation_revision']=e.get('citation_revision','e90cf2f80 (instruction matched from cu-bound3)')
  if 'addr' in e and e['role']!='pool':
   aa=e['addr'] if isinstance(e['addr'],list) else [e['addr']];bb=[addr(a) for a in aa];e['addr']=[a for a in bb if a]
   if not e['addr']:continue
  rr.append(e)
 r[key]=rr
r['target_revision']='fa894d83d (frozen verifier source b2727acd3)'
json.dump(r,open(out,'w'),indent=1);json.dump(mp,open(mapping,'w'),indent=1)
print('rules rebased',sum(bool(x['new']) for x in mp.values()),'of',len(mp));print('unmapped',[(k,v['old_function']) for k,v in mp.items() if not v['new']])
