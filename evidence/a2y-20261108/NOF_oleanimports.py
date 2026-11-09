import struct,sys,json,os
def imports(path):
  d=open(path,'rb').read()
  base,root=struct.unpack_from('<QQ',d,80)
  def obj(p): return p-base
  def hdr(o): rc,cs,other,tag=struct.unpack_from('<iHBB',d,o); return other,tag
  def field(o,i): return struct.unpack_from('<Q',d,o+8+8*i)[0]
  def string(p):
    o=obj(p); other,tag=hdr(o); assert tag==249
    sz=struct.unpack_from('<Q',d,o+8)[0]; return d[o+32:o+32+sz-1].decode()
  def name(p):
    if p==1: return []
    o=obj(p); other,tag=hdr(o)
    if tag==1: return name(field(o,0))+[string(field(o,1))]
    if tag==2: return name(field(o,0))+[str(field(o,1)>>1)]
    raise Exception('name tag %d'%tag)
  r=obj(root); arr=obj(field(r,0)); other,tag=hdr(arr); assert tag==246,tag
  n=struct.unpack_from('<Q',d,arr+8)[0]
  out=[]
  for i in range(n):
    imp=obj(struct.unpack_from('<Q',d,arr+24+8*i)[0])
    out.append('.'.join(name(field(imp,0))))
  return out
if __name__=='__main__':
  roots=json.load(open(sys.argv[1])); start=sys.argv[2:]
  def resolve(m):
    parts=m.split('.'); pkg=parts[0]
    for r in roots:
      if os.path.isdir(os.path.join(r,pkg)) or os.path.exists(os.path.join(r,pkg+'.olean')):
        return os.path.join(r,*parts)+'.olean'
    return None
  seen={};stack=list(start);par={s:None for s in start};bad=[]
  while stack:
    m=stack.pop()
    if m in seen: continue
    p=resolve(m); seen[m]=p
    if p is None or not os.path.exists(p): bad.append((m,p)); continue
    for x in imports(p):
      if x not in par: par[x]=m
      stack.append(x)
  print('modules',len(seen),'missing',len(bad))
  for m,p in bad:
    chain=[];x=m
    while x: chain.append(x); x=par.get(x)
    print('MISSING',m,p); print('  chain',' <- '.join(chain))
