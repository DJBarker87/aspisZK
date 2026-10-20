#!/usr/bin/env python3
"""Certify the exact candidate-1 immutable binder and identical shared tail.

This is a source-prefix interpretation, not admission of failed whole-claim
Aeneas output. It retains the arbitrary execution semantics of every tail token.
"""
from pathlib import Path
import argparse,hashlib,json,re,subprocess
p=argparse.ArgumentParser();p.add_argument('--check',action='store_true');args=p.parse_args()
tool=Path(__file__).resolve().parent;area=tool.parents[1];repo=tool.parents[4]
sha=lambda b:hashlib.sha256(b).hexdigest();candidate='3ab4faf7f5b488a0c82720717656a0ebf4c46efa'
parent=subprocess.check_output(['git','-C',str(repo),'rev-parse',candidate+'^'],text=True).strip()
path='crates/aspis-r1-cost-probe/src/verifier.rs';cuts={}
def fragment(rev):
 data=subprocess.check_output(['git','-C',str(repo),'show',rev+':'+path]);marker=b'fn prepared_claim<H:Digest32>';a=data.index(marker);b=data.index(b'{',a);d=1;e=b+1
 while d:d+=(data[e:e+1]==b'{')-(data[e:e+1]==b'}');e+=1
 cuts[rev]=dict(path=path,file_sha256=sha(data),start_byte=a,end_byte_exclusive=e,source_text_sha256=sha(data[a:e]));return data[a:e]
old=fragment(parent);new=fragment(candidate)
assert old.replace(b'gamma:E',b'g:&[E;29]',1).replace(b'let g=powers::<29>(gamma);',b'',1)==new
oldBody=old[old.index(b'{')+1:-1];newBody=new[new.index(b'{')+1:-1]
# This closed fragment has no comments, string/lifetime literals or macros that
# could alter lexical bindings. Reject rather than approximate unfamiliar input.
for body in [oldBody,newBody]:
 assert not any(c in body for c in [b'//',b'/*',b'"',b"'",b'!',b'unsafe',b'asm',b'include'])
def tokens(b):
 s=b.decode('ascii');out=re.findall(r'[A-Za-z_][A-Za-z_0-9]*|[0-9]+|::|=>|\.\.=|\.\.|->|[^\s]',s)
 assert ''.join(out)==re.sub(r'\s+','',s)
 return out
oldTokens=tokens(oldBody);newTokens=tokens(newBody);binder=tokens(b'let g=powers::<29>(gamma);')
assert oldTokens[:len(binder)]==binder and oldTokens[len(binder):]==newTokens
assert 'gamma' not in newTokens
# The table is an immutable local/argument used only for copied indexing.
positions=[i for i,t in enumerate(newTokens) if t=='g'];assert len(positions)==1
assert all(newTokens[i:i+4]==['g','[','l',']'] for i in positions)
assert old.split(b'{',1)[0].replace(b'gamma:E',b'g:&[E;29]')==new.split(b'{',1)[0]
# Retained production copies of both complete new function and old prefix law.
prod='39c2971dd16c95858a4cfd2c9ae35da052eacfa9';assert fragment(prod)==new
quote=lambda s:json.dumps(s,ensure_ascii=True)
listLit=lambda ts:'['+','.join(map(quote,ts))+']'
lean='''import CuSavingsGammaSourceBinding
set_option autoImplicit false
namespace AspisR1.CuSavingsGammaPrefixData
open CuSavingsGammaSourceBinding
-- These two independently obtained token lists are the exact source tails.
def parentTail : List String := '''+listLit(oldTokens[len(binder):])+'''
def candidateTail : List String := '''+listLit(newTokens)+'''
def parentBlock : Block := .powers29 (.tail parentTail)
def candidateBlock : Block := .tail candidateTail

theorem tail_identity : parentTail=candidateTail := by rfl

theorem prefix_identity : parentBlock=.powers29 candidateBlock := by rfl

#print axioms tail_identity
#print axioms prefix_identity
end AspisR1.CuSavingsGammaPrefixData
'''
manifest=dict(candidate=candidate,parent=parent,production_revision=prod,cuts=cuts,binder=binder,old_tail_tokens=oldTokens[len(binder):],new_tail_tokens=newTokens,old_tail_sha256=sha(' '.join(oldTokens[len(binder):]).encode()),new_tail_sha256=sha(' '.join(newTokens).encode()),table_access='Exactly one g[l], by copied value; no mutable borrow, address observation or escaping table reference.',scope='Syntax-directed immutable source binder and common complete tail; no whole-claim Aeneas emission is admitted. The compositional value semantics of safe immutable array binding/indexing is the explicit source interpretation boundary.',lean_sha256=sha(lean.encode()))
outputs={area/'lean/CuSavingsGammaPrefixData.lean':lean.encode(),tool/'gamma-prefix-source-pins.json':(json.dumps(manifest,indent=2)+'\n').encode()}
for path,data in outputs.items():
 if args.check:assert path.read_bytes()==data,path
 else:path.write_bytes(data)
print(json.dumps(dict(check=args.check,parent=parent,tail_tokens=len(newTokens),identical=True)))
