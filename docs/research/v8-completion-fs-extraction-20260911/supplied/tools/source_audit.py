#!/usr/bin/env python3
"""Lexical inventory only. It cannot determine theorem meaning or kernel validity."""
from __future__ import annotations
import argparse,hashlib,json,re
from pathlib import Path


def strip_lean_comments(text:str)->str:
    out=[];i=0;depth=0;line=False;quoted=False
    while i<len(text):
        if line:
            if text[i]=='\n':line=False;out.append('\n')
            else:out.append(' ')
            i+=1;continue
        if depth:
            if text.startswith('/-',i):depth+=1;out.extend('  ');i+=2
            elif text.startswith('-/',i):depth-=1;out.extend('  ');i+=2
            else:out.append('\n' if text[i]=='\n' else ' ');i+=1
            continue
        if quoted:
            if text[i]=='\\':out.extend('  ');i+=2;continue
            if text[i]=='"':quoted=False
            out.append(' ');i+=1;continue
        if text.startswith('--',i):line=True;out.extend('  ');i+=2
        elif text.startswith('/-',i):depth=1;out.extend('  ');i+=2
        elif text[i]=='"':quoted=True;out.append(' ');i+=1
        else:out.append(text[i]);i+=1
    if depth or quoted:raise ValueError('unterminated comment/string')
    return ''.join(out)


def audit(root:Path)->dict:
    files=[];violations=[]
    for path in sorted((root/'lean').rglob('*.lean')):
        text=path.read_text();code=strip_lean_comments(text)
        dangerous=re.findall(r'\b(?:sorry|admit|axiom|native_decide|unsafe)\b',code)
        if dangerous:violations.append({'file':str(path.relative_to(root)),'tokens':dangerous})
        files.append({'path':str(path.relative_to(root)),
            'sha256':hashlib.sha256(path.read_bytes()).hexdigest(),
            'imports':re.findall(r'^import\s+(\S+)',code,re.M),
            'theorem_count':len(re.findall(r'\b(?:theorem|lemma)\s+',code)),
            'axiom_audit_count':len(re.findall(r'^#print axioms ',code,re.M)),
            'status':'NOT_COMPILED',
            'premise_review_required':True})
    return {'status':'LEXICAL_PASS_ONLY' if not violations else 'LEXICAL_FAIL',
            'files':files,'violations':violations,
            'warning':'No axioms declared lexically does not prove nonvacuity or trusted imports.'}

if __name__=='__main__':
    p=argparse.ArgumentParser();p.add_argument('--root',type=Path,default=Path(__file__).resolve().parents[1]);p.add_argument('--out',type=Path)
    a=p.parse_args();r=audit(a.root)
    if a.out:a.out.parent.mkdir(parents=True,exist_ok=True);a.out.write_text(json.dumps(r,indent=2)+'\n')
    print(json.dumps({k:v for k,v in r.items() if k!='files'},indent=2))
    raise SystemExit(bool(r['violations']))
