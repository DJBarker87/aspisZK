#!/usr/bin/env python3
"""Conservative lexical census, not a Lean parser or call-graph proof.
Keep every monadic bind, total lift, and direct scalar/index tail; retaining
child calls makes unsupported library/caller boundaries visible. No inference
that lift(cast/checked_*) can fail: those operations are explicitly total.
"""
import hashlib, json, re, sys
from pathlib import Path
DEF = re.compile(r"(?:^|\n)(?:@\[[^\]]*\]\s*)?def\s+([\w.«»]+)")
BIND = re.compile(r"\blet\s+[^\n]*?←\s*")
DIRECT = re.compile(r"(?:^|\n)\s*(?:then |else )?(?:x\w* - |(?:Array|Slice)\.(?:index_usize|update)|core\.slice\.index\.Slice\.index)")

def scan(path):
    src = Path(path).read_text()
    matches = list(DEF.finditer(src))
    out = []
    for i, d in enumerate(matches):
        end = matches[i+1].start() if i+1 < len(matches) else len(src)
        body = src[d.end():end]
        ops = []
        for m, is_bind in [(m, True) for m in BIND.finditer(body)] + [(m, False) for m in DIRECT.finditer(body)]:
            start = d.end()+m.start()
            line = src.count('\n',0,start)+1
            # Include continuation lines until the next monadic declaration or branch.
            tail = src[d.end()+(m.end() if is_bind else m.start()):end].lstrip()
            stop = re.search(r"\n\s*(?:let |if |then|else|match |\||ok |end |/--|--|#)",tail)
            expr = tail[:stop.start() if stop else len(tail)].strip()
            text = " ".join(expr.split())
            if text.startswith('lift '):
                kind = 'total_lift'
            elif re.search(r"(?:Array|Slice|Vec)\.(?:index|update)|Slice\.index",text):
                kind = 'index_or_update'
            elif re.search(r" [+*/%-] | >>> | <<< ", ' '+text+' '):
                kind = 'scalar'
            else:
                kind = 'child_call_or_control'
            ops.append({'line':line,'kind':kind,'expression':text})
        if ops:
            out.append({'function':d.group(1),'operations':sorted(ops,key=lambda x:x['line'])})
    return {'file':str(path),'sha256':hashlib.sha256(src.encode()).hexdigest(),'functions':out}

if __name__ == '__main__':
    print(json.dumps([scan(p) for p in sys.argv[1:]],indent=2))
