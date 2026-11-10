#!/usr/bin/env python3
"""NPK_ cfg scanner: list items whose #[cfg]/#[cfg_attr]/cfg!() predicate mentions a prover-implying
feature ("prover", "r1p-check"), with line ranges, and evaluate each predicate under the deployed
verifier configuration (SBF, prover off) and with prover on.
Library use: scan(text, features_on) -> list of dicts.  Heuristic item-extent scanner (comments,
strings, char literals and lifetimes handled); every reported range is re-checkable by hand."""
import re
PROVERISH={'prover','r1p-check'}
def _tok_pred(s):
    return re.findall(r'[A-Za-z_][A-Za-z0-9_]*|"(?:[^"\\]|\\.)*"|[(),=]',s)
def eval_pred(pred,features,target_os='solana',test=False):
    t=_tok_pred(pred); i=0; unknown=[]
    def term():
        nonlocal i
        name=t[i]; i+=1
        if i<len(t) and t[i]=='(' and name in('all','any','not'):
            i+=1; vals=[]
            while t[i]!=')':
                vals.append(term())
                if t[i]==',': i+=1
            i+=1
            return all(vals) if name=='all' else any(vals) if name=='any' else (not vals[0])
        if i<len(t) and t[i]=='=':
            i+=1; v=t[i][1:-1]; i+=1
            if name=='feature': return v in features
            if name=='target_os': return v==target_os
            if name=='target_arch': return v==('sbf' if target_os=='solana' else 'x86_64')
            unknown.append(f'{name}={v}'); return False
        if name=='test': return test
        if name=='debug_assertions': return False
        unknown.append(name); return False
    r=term(); return r,unknown
def _skip_ws_comments(s,i):
    while i<len(s):
        if s[i].isspace(): i+=1
        elif s.startswith('//',i): i=s.find('\n',i); i=len(s) if i<0 else i
        elif s.startswith('/*',i):
            d=0
            while i<len(s):
                if s.startswith('/*',i): d+=1;i+=2
                elif s.startswith('*/',i): d-=1;i+=2
                else: i+=1
                if d==0: break
        else: break
    return i
def _match(s,i):
    """s[i] is an opening bracket; return index after its match, skipping strings/comments/chars."""
    pairs={'(':')','[':']','{':'}'}; stack=[]
    while i<len(s):
        c=s[i]
        if s.startswith('//',i): i=s.find('\n',i); i=len(s) if i<0 else i; continue
        if s.startswith('/*',i): i=_skip_ws_comments(s,i); continue
        if c=='"' or (c=='r' and re.match(r'r#*"',s[i:i+4]) and (i==0 or not (s[i-1].isalnum() or s[i-1]=='_'))):
            m=re.match(r'r(#*)"',s[i:]) if c=='r' else None
            if m:
                end='"'+m.group(1); j=s.find(end,i+len(m.group(0))); i=j+len(end); continue
            j=i+1
            while s[j]!='"': j+= 2 if s[j]=='\\' else 1
            i=j+1; continue
        if c=="'":
            m=re.match(r"'(\\.|\\u\{[0-9a-fA-F]+\}|\\x..|[^\\'])'",s[i:])
            if m: i+=len(m.group(0)); continue
            i+=1; continue  # lifetime
        if c in pairs: stack.append(pairs[c])
        elif c in ')]}':
            stack.pop()
            if not stack: return i+1
        i+=1
    return i
def _item_end(s,i):
    """From start of item at i: end index (exclusive)."""
    depth=0; j=i
    km=re.match(r'\s*(?:pub(?:\([^)]*\))?\s+)?(?:unsafe\s+|async\s+|extern\s+"C"\s+)*(let|fn|struct|enum|union|impl|trait|mod|use|const|static|type|macro_rules!|extern\s+crate)\b',s[i:])
    kind=km.group(1) if km else None
    kw = kind in ('let','use','const','static','type')      # end at ';' only
    decl = kind in ('fn','struct','enum','union','impl','trait','mod','macro_rules!','extern crate')  # end at body or ';'
    commas_end = kind is None
    while j<len(s):
        j2=_skip_ws_comments(s,j)
        if j2!=j: j=j2; continue
        c=s[j]
        if c in '([{':
            k=_match(s,j)
            if c=='{' and not kw:
                n=_skip_ws_comments(s,k)
                if n<len(s) and s[n] in ';,': return n+1
                if n<len(s) and s[n]=='.' : j=k; continue
                if n<len(s) and s.startswith('else',n): j=k; continue
                return k
            j=k; continue
        if c==';' or (c==',' and commas_end): return j+1
        if c in ')]}': return j
        if c=='"' or c=="'":
            if c=='"':
                k=j+1
                while s[k]!='"': k+= 2 if s[k]=='\\' else 1
                j=k+1; continue
            mm=re.match(r"'(\\.|\\x..|[^\\'])'",s[j:]); j+= len(mm.group(0)) if mm else 1; continue
        j+=1
    return j
def _name(text):
    t=re.sub(r'#!?\[[^\]]*\]','',text).strip()
    m=re.match(r'(?:pub(?:\([^)]*\))?\s+)?(?:unsafe\s+|const\s+|async\s+|extern\s+"C"\s+)*(fn|struct|enum|mod|trait|type|const|static|use|let|macro_rules!|impl)\b\s*([^\s({<;=:]*)',t)
    if m:
        if m.group(1)=='let': return ' '.join(t.split('=')[0].split())[:100]
        if m.group(1)=='impl':
            h=t.split('{')[0]; return 'impl '+' '.join(h[4:].split())[:120]
        return f'{m.group(1)} {m.group(2)}'
    return ' '.join(t.split())[:80]
def scan(text,features_off,prover_feats=PROVERISH):
    lines_at=[0]
    for k,ch in enumerate(text):
        if ch=='\n': lines_at.append(k+1)
    import bisect
    ln=lambda pos: bisect.bisect_right(lines_at,pos)
    out=[]
    for m in re.finditer(r'#(!?)\[\s*(cfg|cfg_attr)\s*\(|cfg!\s*\(',text):
        # skip matches inside line comments
        ls=text.rfind('\n',0,m.start())+1
        if '//' in text[ls:m.start()]: continue
        if m.group(0).startswith('cfg!'):
            po=m.end()-1; pe=_match(text,po); pred=text[po+1:pe-1]; kind='cfg!'; inner=False; a_end=pe
        else:
            inner=m.group(1)=='!'; kind=m.group(2)
            po=m.end()-1; pe=_match(text,po); pred=text[po+1:pe-1]
            if kind=='cfg_attr':
                # predicate is the first top-level argument
                d=0; cut=len(pred)
                for k,ch in enumerate(pred):
                    if ch in '([': d+=1
                    elif ch in ')]': d-=1
                    elif ch==',' and d==0: cut=k; break
                pred=pred[:cut]
            a_end=_match(text,m.start()+1+len(m.group(1)))  # end of #[...]
        feats=set(re.findall(r'feature\s*=\s*"([^"]+)"',pred))
        if not feats & prover_feats: continue
        v,unk=eval_pred(pred,features_off)
        p,_=eval_pred(pred,features_off|prover_feats|{'prover'})
        if kind=='cfg!' : start=m.start(); end=a_end; name='cfg!(...) expression'
        elif inner: start=m.start(); end=len(text); name='whole file (inner attribute)'
        else:
            st=a_end
            while True:
                st=_skip_ws_comments(text,st)
                if text.startswith('#[',st): st=_match(text,st+1); continue
                break
            start=m.start(); end=_item_end(text,st); name=_name(text[st:end])
        out.append(dict(kind=kind,predicate=' '.join(pred.split()),line_start=ln(start),line_end=ln(max(end-1,start)),
                        item=name,in_verifier=v,with_prover=p,prover_dependent=(v!=p),unknown_atoms=unk))
    return out
