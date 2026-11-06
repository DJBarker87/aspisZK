#!/usr/bin/env python3
"""Lexical Rust loop/post-loop exit candidate finder; preserves byte offsets.
It deliberately overapproximates control flow; no reachability verdict is inferred.
"""
import re

def mask(source):
    # Tokenize comments and quoted literals; nested block comments handled explicitly.
    out=list(source);i=0
    while i<len(source):
        if source.startswith('//',i):
            e=source.find('\n',i);e=len(source) if e<0 else e
        elif source.startswith('/*',i):
            e=i+2;depth=1
            while e<len(source) and depth:
                if source.startswith('/*',e):depth+=1;e+=2
                elif source.startswith('*/',e):depth-=1;e+=2
                else:e+=1
        elif source[i]=='"':
            e=i+1
            while e<len(source):
                if source[e]=='\\':e+=2
                elif source[e]=='"':e+=1;break
                else:e+=1
        elif source[i]=="'" and re.match(r"'(?:\\.|[^'\\])'",source[i:]):
            e=i+len(re.match(r"'(?:\\.|[^'\\])'",source[i:]).group())
        else:i+=1;continue
        for j in range(i,e):
            if out[j]!='\n':out[j]=' '
        i=e
    return ''.join(out)

def scan(source,base_line=1):
    text=mask(source);stack=[];pairs={}
    for i,c in enumerate(text):
        if c=='{':stack.append(i)
        elif c=='}' and stack:pairs[stack.pop()]=i
    loops=[]
    for m in re.finditer(r'\b(?:while|for|loop)\b',text):
        brace=text.find('{',m.end())
        if brace<0 or brace not in pairs:continue
        # Do not treat `impl X for Y` as a loop.
        if re.search(r'\bimpl\b[^{};]*$',text[:m.start()]):continue
        loops.append((m.start(),pairs[brace]))
    exits=[]
    for m in re.finditer(r'\breturn\b|\?|\bbreak\b',text):
        prior=[(a,b) for a,b in loops if b<m.start()]
        if prior:
            exits.append({'line':base_line+text.count('\n',0,m.start()),'kind':m.group(),
                          'after_loop_end_lines':sorted({base_line+text.count('\n',0,b) for _,b in prior}),
                          'inside_another_loop':any(a<m.start()<b for a,b in loops)})
    return {'loop_count':len(loops),'post_loop_exit_candidates':exits}

def function_span(source,name,near_line):
    text=mask(source); matches=list(re.finditer(r'\bfn\s+'+re.escape(name)+r'\b',text))
    if not matches:return None
    m=min(matches,key=lambda x:abs(text.count('\n',0,x.start())+1-near_line))
    brace=text.find('{',m.end())
    if brace<0:return None
    depth=0
    for end in range(brace,len(text)):
        if text[end]=='{':depth+=1
        elif text[end]=='}':
            depth-=1
            if not depth:break
    else:return None
    return {'start_line':text.count('\n',0,m.start())+1,'end_line':text.count('\n',0,end)+1,'text':source[m.start():end+1]}
