#!/usr/bin/env python3
"""Authenticate the source/model M31 chain schedule; not a Rust extractor."""
import argparse,hashlib,json,re
from pathlib import Path
def function(s,needle):
    start=s.index(needle);brace=s.index('{',start);depth=0
    for i in range(brace,len(s)):
        depth+=(s[i]=='{')-(s[i]=='}')
        if depth==0:return s[brace+1:i]
    raise AssertionError(needle)
def clean(s):return re.sub(r'\s+','',re.sub(r'//[^\n]*','',s))
def rust_expr(s):
    tokens=re.findall(r'\w+|[().,]',s);i=0
    def expr():
        nonlocal i
        name=tokens[i];i+=1
        if name=='square_n':
            assert tokens[i]=='(';i+=1;v=expr();assert tokens[i]==',';i+=1
            n=int(tokens[i]);i+=1;assert tokens[i]==')';i+=1;node=['squares',n,v]
        else:node='x' if name=='self' else name
        while i<len(tokens) and tokens[i]=='.':
            assert tokens[i:i+3]==['.','mul','('];i+=3;v=expr();assert tokens[i]==')';i+=1;node=['mul',node,v]
        return node
    out=expr();assert i==len(tokens);assert ''.join(tokens)==clean(s);return out
def lean_expr(s):
    tokens=re.findall(r'\w+|[()]',s);i=0
    def expr():
        nonlocal i
        name=tokens[i];i+=1
        if name=='(':
            node=expr();assert tokens[i]==')';i+=1;return node
        if name=='mul':return ['mul',expr(),expr()]
        if name=='squares':
            assert tokens[i]=='mul';i+=1;n=int(tokens[i]);i+=1;return ['squares',n,expr()]
        return name
    out=expr();assert i==len(tokens);assert ''.join(tokens)==clean(s);return out
def schedules(field,lean):
    square=clean(function(field,'fn square_n(mut value: M31, count: usize) -> M31'))
    assert square=='for_in0..count{value=value.mul(value);}value'
    body=clean(function(field,'pub fn inv(self) -> M31'))
    guard='assert!(self.0!=0,"inverseofzero");';assert body.startswith(guard);body=body[len(guard):]
    parts=body.split(';');rust=[]
    for line in parts[:-1]:
        match=re.fullmatch(r'let(\w+)=(.*)',line);assert match
        rust.append([match[1],rust_expr(match[2])])
    rust.append(['return',rust_expr(parts[-1])])
    model=lean.split('def chain {A : Type*}',1)[1].split('\ntheorem ',1)[0].split(': A :=',1)[1]
    proof=[]
    for line in model.strip().splitlines():
        match=re.fullmatch(r'\s*let (\w+) := (.*)',line)
        proof.append([match[1],lean_expr(match[2])]if match else['return',lean_expr(line)])
    assert rust==proof,(rust,proof)
    assert [x[0]for x in rust]==['t2','t4','t8','t16','t24','t28','t29','t30','return']
    def cost(x):return 0 if isinstance(x,str) else (1+cost(x[1])+cost(x[2])if x[0]=='mul' else x[1]+cost(x[2]))
    assert sum(cost(x[1])for x in rust)==38
    return rust
def audit(field,lean):
    schedule=schedules(field,lean);negatives=0
    mutants=[(field.replace('square_n(t16, 8)','square_n(t16, 7)',1),lean),
        (field.replace('assert!(self.0 != 0, "inverse of zero");','',1),lean),
        (field.replace('value = value.mul(value);','value = value.mul(M31::ONE);',1),lean),
        (field,lean.replace('squares mul 8 t16','squares mul 7 t16',1)),
        (field,lean.replace('mul (mul t30 t30) x','mul t30 x',1))]
    for f,l in mutants:
        assert (f,l)!=(field,lean)
        try:schedules(f,l)
        except (AssertionError,ValueError,IndexError):negatives+=1
        else:raise AssertionError('accepted changed schedule/guard')
    return {'matched_bindings':len(schedule),'base_multiplications':38,'negative_mutations_rejected':negatives,
        'schedule':schedule,'scope':'structural chain and square-loop audit; not generated Result-loop or compiler refinement',
        'universal_Rust_refinement':False}
if __name__=='__main__':
    p=argparse.ArgumentParser();p.add_argument('--field',type=Path,required=True);p.add_argument('--lean',type=Path,required=True);p.add_argument('--output',type=Path);a=p.parse_args()
    result=audit(a.field.read_text(),a.lean.read_text())
    result.update(field_sha256=hashlib.sha256(a.field.read_bytes()).hexdigest(),lean_sha256=hashlib.sha256(a.lean.read_bytes()).hexdigest())
    if a.output:
        assert not a.output.exists();a.output.write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps(result,indent=2))
