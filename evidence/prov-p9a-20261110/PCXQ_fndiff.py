#!/usr/bin/env python3
"""PCXQ step 1: function/item-level diff 4bb3b3f vs 271869c946d for the three non-test files. Items: fn, struct, enum, const, static, type.
Key = (enclosing impl/mod chain, item name, occurrence); text compared after whitespace normalisation and comment removal."""
import subprocess,re,json,hashlib,sys
sys.dont_write_bytecode=True
OLD='4bb3b3f51e16b4525f1d10336e2b0bcbbd775387';NEW='271869c946d4286db6ee5be784f136599fa8707e'
FILES=['crates/aspis-statement/src/pool_v1/pair_forest_semantic_terminal.rs','programs/r1-cost-probe/src/pool_route.rs','programs/r1-cost-probe/src/r1_pool_adapter.rs']
def show(rev,f):return subprocess.check_output(['git','show',rev+':'+f],text=True)
def strip_comments(s):
    s=re.sub(r'(?m)//.*$','',s);return re.sub(r'/\*.*?\*/','',s,flags=re.S)
norm=lambda s:re.sub(r'\s+','',strip_comments(s))
ITEM=re.compile(r'(?m)^[ \t]*((?:#\[[^\n]*\]\s*)*)(?:pub(?:\([a-z:]+\))?\s+)?(?:const\s+)?(?:unsafe\s+)?(fn|struct|enum|const|static|type|mod|impl|trait)\b\s*(?:<[^>{]*>\s*)?([A-Za-z_][A-Za-z0-9_]*|[^\n{]*?)(?=[\s<({:;=])')
def items(src):
    out=[];stack=[]  # (name, end_index)
    i=0
    for m in ITEM.finditer(src):
        kind=m.group(2);name=m.group(3).strip() if kind!='impl' else re.sub(r'\s+',' ',src[m.start(2):src.index('{',m.start(2))]).strip()
        start=m.start()
        # find end: first '{' or ';' at depth 0 after the header (skip generics/where/strings roughly)
        j=m.end();depth=0
        while j<len(src):
            c=src[j]
            if c=='"':
                j+=1
                while src[j]!='"':j+=2 if src[j]=='\\' else 1
            elif c in '([':depth+=1
            elif c in ')]':depth-=1
            elif c=='{' and depth==0:break
            elif c==';' and depth==0:break
            j+=1
        if j>=len(src):continue
        if src[j]==';':end=j+1
        else:
            d=0;k=j
            while k<len(src):
                c=src[k]
                if c=='"':
                    k+=1
                    while src[k]!='"':k+=2 if src[k]=='\\' else 1
                elif c=="'" and re.match(r"'(\\.|[^'\\])'",src[k:k+4]):
                    k+=len(re.match(r"'(\\.|[^'\\])'",src[k:k+4]).group(0))-1
                elif c=='{':d+=1
                elif c=='}':
                    d-=1
                    if d==0:break
                k+=1
            end=k+1
        while stack and stack[-1][1]<=start:stack.pop()
        chain='/'.join(s[0] for s in stack)
        if kind in('mod','impl','trait'):stack.append((kind+' '+name,end));
        out.append(dict(chain=chain,kind=kind,name=name,start=start,end=end,text=src[start:end],line=src.count('\n',0,start)+1))
    return out
def keyed(its):
    seen={};r={}
    for it in its:
        if it['kind'] in('mod','impl','trait') and False:continue
        k=(it['chain'],it['kind'],it['name']);n=seen.get(k,0);seen[k]=n+1;r[k+(n,)]=it
    return r
res=dict(old=OLD,new=NEW,files={})
for f in FILES:
    a=keyed(items(show(OLD,f)));b=keyed(items(show(NEW,f)))
    rows=[]
    for k in sorted(set(a)|set(b)):
        A=a.get(k);B=b.get(k)
        if A and B:
            # container items: compare only header (their body items are keyed separately); leaf: whole text
            if A['kind'] in('mod','impl','trait'):continue
            st='unchanged' if norm(A['text'])==norm(B['text']) else 'changed'
        elif A:st='removed'
        else:st='added'
        if k[1]=='fn' or st!='unchanged' :
            if st=='unchanged':continue
            T=B or A
            if '#[cfg(test)]' in T['text'] or 'mod tests' in T['chain'] or 'mod public_serializer_tests' in T['chain'] or 'close_checkpoint_tests' in T['chain'] or 'rw_tests' in T['chain']:t='test'
            else:t='prod'
            rows.append(dict(chain=k[0],kind=k[1],name=k[2],status=st,scope=t,old_line=A and A['line'],new_line=B and B['line'],old_sha256=A and hashlib.sha256(norm(A['text']).encode()).hexdigest(),new_sha256=B and hashlib.sha256(norm(B['text']).encode()).hexdigest()))
    res['files'][f]=rows
json.dump(res,open('PIN2_FUNCTION_DIFF.json','w'),indent=1)
for f,rows in res['files'].items():
    print(f)
    for r in rows:print(' ',r['scope'],r['status'],r['kind'],r['chain'][:60],r['name'])
