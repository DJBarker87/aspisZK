#!/usr/bin/env python3
"""Compare a restricted emitted-Lean token stream, retaining comments/literals.

This is an emission provenance check, not a Lean parser or a semantics theorem.
Whitespace outside tokens is ignored. Strings, nested comments, and quoted
identifier contents are compared byte-for-byte. Unknown syntax fails closed.
The final emission still requires actual Lean compilation and axioms audits.
"""
import argparse
import hashlib
import json
import unicodedata
from pathlib import Path

SYMBOLS = sorted([':=', '=>', '->', '←', '→', '<-', '==', '!=', '<=', '>=',
                  '&&', '||', '×', '∧', '∨', '¬', '≤', '≥', '≠', '↔', '↑', '↓',
                  '(', ')', '[', ']', '{', '}', ':', ',', ';', '.', '|', '=',
                  '<', '>', '+', '-', '*', '/', '%', '!', '#', '@', '?', '&'],
                 key=len, reverse=True)

def first(c):
    return c == '_' or unicodedata.category(c).startswith('L')

def rest(c):
    return first(c) or c.isdigit() or c == "'" or unicodedata.category(c).startswith('M')

def tokens(s):
    out=[]; i=0
    def segment(j):
        if s[j]=='«':
            end=s.find('»',j+1)
            if end<0: raise ValueError('Unterminated quoted identifier')
            return end+1
        if not first(s[j]): raise ValueError('Invalid identifier segment')
        j+=1
        while j<len(s) and rest(s[j]): j+=1
        return j
    while i<len(s):
        if s[i].isspace(): i+=1; continue
        start=i
        if s.startswith('--',i):
            j=s.find('\n',i); i=len(s) if j<0 else j; kind='line-comment'
        elif s.startswith('/-',i):
            depth=1; i+=2
            while depth:
                if i>=len(s): raise ValueError('Unterminated block comment')
                if s.startswith('/-',i): depth+=1; i+=2
                elif s.startswith('-/',i): depth-=1; i+=2
                else: i+=1
            kind='block-comment'
        elif s[i]=='"':
            i+=1
            while True:
                if i>=len(s): raise ValueError('Unterminated string')
                if s[i]=='\\':
                    if i+1>=len(s): raise ValueError('Unterminated string escape')
                    i+=2
                elif s[i]=='"': i+=1; break
                else: i+=1
            kind='string'
        elif first(s[i]) or s[i]=='«':
            i=segment(i)
            while i+1<len(s) and s[i]=='.' and (first(s[i+1]) or s[i+1]=='«'):
                i=segment(i+1)
            kind='identifier'
        elif s[i].isascii() and s[i].isdigit():
            i+=1
            while i<len(s) and s[i].isascii() and s[i].isdigit(): i+=1
            kind='numeral'
        else:
            symbol=next((x for x in SYMBOLS if s.startswith(x,i)),None)
            if symbol is None: raise ValueError(f'Unclassified syntax at offset {i}: {s[i:i+24]!r}')
            i+=len(symbol); kind='symbol'
        out.append((kind,s[start:i]))
    return out

def main():
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('original',type=Path); ap.add_argument('candidate',type=Path)
    a=ap.parse_args(); old=a.original.read_bytes(); new=a.candidate.read_bytes()
    left=tokens(old.decode()); right=tokens(new.decode())
    equal=left==right
    result={'original_sha256':hashlib.sha256(old).hexdigest(),
            'candidate_sha256':hashlib.sha256(new).hexdigest(),
            'original_tokens':len(left),'candidate_tokens':len(right),
            'token_sequences_equal':equal,
            'boundary':'Restricted lexical provenance only; Lean layout and semantics require the separate compile/audit gate.'}
    if not equal:
        k=next((i for i,(x,y) in enumerate(zip(left,right)) if x!=y),min(len(left),len(right)))
        result['first_difference']={'index':k,'original':left[k] if k<len(left) else None,'candidate':right[k] if k<len(right) else None}
    print(json.dumps(result,indent=2)); raise SystemExit(0 if equal else 2)

if __name__=='__main__':main()
