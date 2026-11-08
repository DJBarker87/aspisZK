import re,hashlib
docrx=re.compile(r'/--\s*\[([^\]]+)\]:?(.*?)-/',re.S)
crate_rx=re.compile(r'\b[a-z][a-z0-9_]*(?=::)')
def symnorm(sym):
    # replace first path component and any crate-like component following '{' or '<' or start
    s=re.sub(r'(^|[{<,\s(&])([a-z][a-z0-9_]*)::',lambda m:m.group(1)+'CRATE::' if m.group(2) not in ('core','alloc','std') else m.group(0),sym)
    return s
def strip_comments(t):
    t=re.sub(r'/-.*?-/','',t,flags=re.S)
    t=re.sub(r'--[^\n]*','',t)
    return t
def segments(text):
    out=[]
    ms=list(docrx.finditer(text))
    for i,m in enumerate(ms):
        end=ms[i+1].start() if i+1<len(ms) else len(text)
        body=text[m.end():end]
        # cut at trailing 'end <ns>' or 'namespace'
        body=re.split(r'(?m)^end\b|^namespace\b',body)[0]
        src=re.search(r"Source: '([^']+)'",m.group(2))
        norm=' '.join(strip_comments(body).split())
        out.append({'sym':m.group(1).strip(),'symn':symnorm(m.group(1).strip()),'src':src.group(1) if src else None,
                    'norm_sha':hashlib.sha256(norm.encode()).hexdigest(),'head':norm[:80]})
    return out
