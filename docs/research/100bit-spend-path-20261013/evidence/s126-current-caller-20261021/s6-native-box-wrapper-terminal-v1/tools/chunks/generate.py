#!/usr/bin/env python3
"""Complete native scalar observer, exact boxed-wrapper span, native helpers."""
from pathlib import Path
import re
import subprocess
import sys

R = Path(__file__).resolve().parents[2]
REV = '4bb3b3f51e16b4525f1d10336e2b0bcbbd775387'
D = Path(__file__).parent
classes = {
 'pair_forest_terminal': ['PoolV1PairForestTerminalCommonV1'],
 'payment_relation': ['PoolV1PrivateTransferPublicV1', 'PoolV1WithdrawalPublicV1'],
 'pair_tree_profile': ['PoolV1PairLatePublicStatementV1', 'PoolV1PairLiveSnapshotV1'],
 'pair_terminal': ['PoolV1PairVerifiedAfterstateV1'],
}
fields = {}
for module, names in classes.items():
    source = subprocess.check_output(['git','show',REV+':crates/aspis-statement/src/pool_v1/'+module+'.rs'],cwd=R,text=True)
    for name in names:
        match = re.search(r'pub struct '+name+r'\s*\{([^}]+)\}',source,re.S)
        assert match
        body = '\n'.join(l for l in match[1].splitlines() if not l.strip().startswith('//'))
        fs = re.findall(r'pub\s+(\w+):\s*([^\n]+?),\s*(?:\n|$)',body)
        assert len(fs)==body.count('pub ')
        fields[name] = fs

def flatten(t, prefix):
    t=t.strip()
    if t in ['u8','u32','u64']:
        return [prefix+' as u64']
    if t=='M31':
        return [prefix+'.0 as u64']
    if t=='Digest':
        return [prefix+'['+str(i)+'].0 as u64' for i in range(8)]
    if t.startswith('['):
        m=re.fullmatch(r'\[(.+);\s*(.+)\]',t);assert m
        n={'32':32,'POOL_V1_PAIR_TREE_DEPTH':20,'super::POOL_V1_PAIR_TREE_DEPTH':20}[m[2].strip()]
        return [term for i in range(n) for term in flatten(m[1],prefix+'['+str(i)+']')]
    return [term for name,typ in fields[t] for term in flatten(typ,prefix+'.'+name)]

def families(t,prefix,depth=0):
    t=t.strip()
    if t in ['u8','u32','u64']:
        return [(prefix+' as u64',[])]
    if t=='M31':
        return [(prefix+'.0 as u64',[])]
    if t=='Digest':
        return [(prefix+'['+['i','j'][depth]+'%8].0 as u64',[8])]
    if t.startswith('['):
        m=re.fullmatch(r'\[(.+);\s*(.+)\]',t);assert m
        n={'32':32,'POOL_V1_PAIR_TREE_DEPTH':20,'super::POOL_V1_PAIR_TREE_DEPTH':20}[m[2].strip()]
        assert depth<2
        return [(term,[n]+dims) for term,dims in families(m[1],prefix+'['+['i','j'][depth]+'%'+str(n)+']',depth+1)]
    return [row for name,typ in fields[t] for row in families(typ,prefix+'.'+name,depth)]

observer='    fn observe(s:&Statement,family:u8,i:usize,j:usize)->u64 {\n        match s {\n'
counts={};coverage={}
for variant,payment,tag in [('PrivateTransfer','PoolV1PrivateTransferPublicV1',1),('Withdrawal','PoolV1WithdrawalPublicV1',2)]:
    groups=[(str(tag)+'u64',[])]+families('PoolV1PairForestTerminalCommonV1','common')+families(payment,'public')
    expected=[str(tag)+'u64']+flatten('PoolV1PairForestTerminalCommonV1','common')+flatten(payment,'public')
    expanded=[]
    for term,dims in groups:
        assert len(dims)<=2
        for i in range(dims[0] if dims else 1):
            for j in range(dims[1] if len(dims)>1 else 1):
                out=term
                for name,value,n in zip(['i','j'],[i,j],dims):
                    out=out.replace('['+name+'%'+str(n)+']','['+str(value)+']')
                expanded.append(out)
    assert expanded==expected,(variant,len(expanded),len(expected))
    counts[variant]=dict(families=len(groups),scalar_coordinates=len(expected))
    coverage[variant]=groups
    observer+='            Statement::'+variant+' {common,public} => match family {\n'
    observer+=''.join('                '+str(index)+'=>'+term+',\n' for index,(term,_) in enumerate(groups))
    observer+='                _=>0,\n            },\n'
observer+='        }\n    }\n'
getter=(R/'tools/s6-native-getter-20261026/proofs.rs').read_text()
a=getter.index('    // BEGIN GENERATED CONSTRUCTORS');b=getter.index('    fn aliases(')
constructors=getter[a:b]
src=subprocess.check_output(['git','show',REV+':programs/r1-cost-probe/src/r1_pool_adapter.rs'],cwd=R,text=True)
a=src.index('fn decode_public_statement_box(');i=src.index('{',a);j=i+1;depth=1
while depth:
    depth+=(src[j]=='{')-(src[j]=='}');j+=1
wrapper=src[a:j]
body=(D/'proof-template.rs').read_text()
body=body.replace('// GENERATED_NATIVE_WRAPPER',wrapper)
body=body.replace('    // GENERATED_CONSTRUCTORS',constructors)
body=body.replace('    // GENERATED_OBSERVER',observer)
byte_helpers='    fn byte32()->[u8;32] {['+','.join('kani::any::<u8>()' for _ in range(32))+']}\n'
byte_helpers+='    fn byte24()->[u8;24] {['+','.join('kani::any::<u8>()' for _ in range(24))+']}\n'
byte_helpers+='    fn bytes1880()->[u8;1880] {\n        let mut bytes=[0u8;1880];\n'
byte_helpers+=''.join('        bytes['+str(i*32)+'..'+str((i+1)*32)+'].copy_from_slice(&byte32());\n' for i in range(58))
byte_helpers+='        bytes[1856..1880].copy_from_slice(&byte24());\n        bytes\n    }\n'
body=body.replace('    // GENERATED_BYTE_HELPERS',byte_helpers)
body=body.replace('    // GENERATED_BYTES','        let bytes=bytes1880();')
if '--check' in sys.argv:
    assert (D/'proofs.rs').read_text()==body
else:
    (D/'proofs.rs').write_text(body)
print('native wrapper generation:',counts)
