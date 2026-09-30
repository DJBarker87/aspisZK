#!/usr/bin/env python3
"""Source-pinned private terminal region; exact integer adder compilation."""
import argparse,ast,collections,hashlib,json,re,shutil
from pathlib import Path
p=argparse.ArgumentParser();p.add_argument('--control',type=Path,required=True);p.add_argument('--output',type=Path,required=True);a=p.parse_args()
src=a.control;dst=a.output;here=Path(__file__).parent
def sha(f):return hashlib.sha256(f.read_bytes()).hexdigest()
assert sha(src/'r18-stage.json')=='1455a58e904b3b803c46de43686c73733b5c58a69f1bf391cc5d5190fbb1a296'
m=json.loads((src/'r18-stage.json').read_text())
for n,h in m['files'].items():assert sha(src/n)==h,n
assert not dst.exists();dst.mkdir()
for n in ['crates','docs','programs','xtask','audit']:
    shutil.copytree(src/n,dst/n,ignore=shutil.ignore_patterns('target','.git','*-keypair.json'))
for n in ['Cargo.toml','Cargo.lock','r17-stage.json','r17-sbf-probe.json','r19_canonical_check.rs',*m['files']]:
    if not(dst/n).exists():(dst/n).parent.mkdir(parents=True,exist_ok=True);shutil.copy2(src/n,dst/n)
ex=dst/'docs/research/v8-no-work-100-20260907/experiments';changed=[]
def save(n,s):
    f=ex/n;f.write_text(s);changed.append(f)
source=(ex/'r22_scalar.rs').read_text();consts={}
for name in ['MASKS','IDS','ENDS','ROWS']:
    consts[name]=ast.literal_eval(re.search(r'const '+name+r':[^=]+=(\[[^;]+\]);',source)[1])
masks,ids,ends,rows=[consts[n]for n in ['MASKS','IDS','ENDS','ROWS']]
assert 'false'not in re.search(r'const COMPLEMENT:[^=]+=(\[[^;]+\]);',source)[1]
sets=[set(rows[ends[i]:ends[i+1]])for i in range(12)]
assert all(len(s)==ends[i+1]-ends[i]and all(0<=x<64 for x in s)for i,s in enumerate(sets))
for low in range(16):assert (1<<64)-1-sum(1<<x for x in sets[ids[low]])==masks[low]
code=['// Exact integer coefficient expansion checked by the source-pinned generator.',
 '#[inline(never)]','fn r106_inactive(hb:&[CQ])->[CQ;19] {','    assert_eq!(hb.len(),128);']
counts=[]
for channel,selected in [(0,list(range(12))),(1,sorted(set(ids[:3])))]:
    targets=[set(range(64))]+[sets[i].copy()for i in selected];original=[s.copy()for s in targets]
    expansions=[collections.Counter({i:1})for i in range(64)];steps=[]
    while True:
        freq=collections.Counter((x,y)for s in targets for x in s for y in s if x<y)
        if not freq:break
        pair,n=max(freq.items(),key=lambda x:(x[1],-x[0][0],-x[0][1]))
        if n<2:break
        a0,b0=pair;idx=64+len(steps);steps.append(pair);expansions.append(expansions[a0]+expansions[b0])
        for s in targets:
            if a0 in s and b0 in s:s.difference_update(pair);s.add(idx)
    def term(i):return f'hb[{64*channel+i}]'if i<64 else f'n{channel}_{i}'
    for j,(x,y)in enumerate(steps):code.append(f'    let n{channel}_{64+j}={term(x)}.add({term(y)});')
    for j,s in enumerate(targets):
        got=collections.Counter()
        for node in s:got.update(expansions[node])
        assert got==collections.Counter({i:1 for i in original[j]})
        terms=[term(x)for x in sorted(s)];expr=terms[0]+''.join(f'.add({t})'for t in terms[1:])
        label='total'if j==0 else str(selected[j-1])
        code.append(f'    let s{channel}_{label}={expr};')
        if j:code.append(f'    let v{channel}_{label}=s{channel}_total.sub(s{channel}_{label});')
    counts.append({'channel':channel,'old_additions':sum(len(s)-1 for s in original),'new_additions':len(steps)+sum(len(s)-1 for s in targets),'integer_coefficients_checked':True})
code.append('    ['+','.join([f'v0_{i}'for i in ids]+[f'v1_{i}'for i in ids[:3]])+']\n}')
save('r106_terminal.rs',(here/'r106_terminal.rs').read_text()+'\n'+'\n'.join(code)+'\n')
f=ex/'r19_channel_ordinary.rs';save(f.name,f.read_text()+'\ninclude!("r106_terminal.rs");\n')
f=ex/'r17_host_relation.rs';s=f.read_text();start=s.index('        let ordinary=crate::r19_channel_ordinary::terminal_scalar(');end=s.index('        // i1=tau*i0',start)
old=s[start:end];assert 'terminal=terminal.add(ordinary).add(sparse.mul(beta.mul(public_audit[10])));'in old
fallback=old.replace('        terminal=terminal.add(ordinary).add(sparse.mul(beta.mul(public_audit[10])));','        ordinary.add(sparse.mul(beta.mul(public_audit[10])))')
new='''        let ordinary_and_sparse=if let Some(coins)=coins {
            crate::r19_channel_ordinary::r106_terminal(&public_audit,p.abc,alphas,beta,
                &core::array::from_fn(|i|finals[i]),&mut workspace,&kernel,coins)
        } else {
'''+fallback+'''        };
        terminal=terminal.add(ordinary_and_sparse);
'''
save(f.name,s[:start]+new+s[end:])
f=ex/'r84_bitperm_check.rs';s=f.read_text();assert s.count('fn main() {')==1
save('r106_terminal_check.rs',s.replace('fn main() {','fn main() {r19_channel_ordinary::r106_controls();'))
f=ex/'performance-host/Cargo.toml';save('performance-host/Cargo.toml',f.read_text()+'\n[[bin]]\nname="r106-terminal-check"\npath="../r106_terminal_check.rs"\n')
for f in changed:m['files'][str(f.relative_to(dst))]=sha(f)
m['r106_native']={'control':str(src),'control_manifest_sha256':sha(src/'r18-stage.json'),
 'protocol_changed':False,'validation_removed':False,'security_promoted':False,'new_security_claim':False,
 'fixtures':m['r105_native']['fixtures'],'changed':len(set(changed)),'adder_schedules':counts}
(dst/'r18-stage.json').write_text(json.dumps(m,indent=2)+'\n')
print(json.dumps({'stage':str(dst),'pins':len(m['files']),'changed':len(set(changed)),'adder_schedules':counts}))
