#!/usr/bin/env python3
"""Add exact frozen layout declarations and checked loop-body splits."""
import argparse,json,re,sys
from pathlib import Path
sys.path.insert(0,str(Path(__file__).resolve().parent))
from prepare import KIT,fn,P,sha
from inventory import blob,walk,text

def normalize(s): return re.sub(r'\s+','',s)
def build(basefiles,pins):
    m=blob('crates/aspis-r1-cost-probe/src/multiproof.rs')
    # Assertions below prevent source/harness drift for each copied split.
    checks=[]
    def bind(fragment,src,harness,owner):
        assert normalize(fragment) in normalize(src),(owner,'source drift')
        assert normalize(fragment) in normalize(harness),(owner,'harness drift')
        checks.append(dict(owner=owner,fragment=fragment,sha256=sha(fragment.encode()),relation='exact whitespace-normalized body fragment; loop setup/state invariant supplied by harness'))
    ch=(KIT/'control-harnesses.rs').read_text()
    node,_=fn(m,'node_count');sort,_=fn(m,'sort_dedup')
    bind('''let parent = index_at(&level, i) >> arity.bits();
            let mut j = i;
            while j < n && index_at(&level, j) >> arity.bits() == parent {
                j += 1;
            }''',node,ch,'node_count::parent_group')
    bind('''let mut j = i;
        while j > 0 && idx[j - 1] > idx[j] {
            idx.swap(j - 1, j);
            val.swap(j - 1, j);
            j -= 1;
        }''',sort,ch,'sort_dedup::insertion_inner')
    bind('''if idx[i] == idx[w - 1] {
            if val[i] != val[w - 1] {
                return None;
            }
        } else {
            idx[w] = idx[i];
            val[w] = val[i];
            w += 1;
        }''',sort,ch,'sort_dedup::dedup_step')
    basefiles['multiproof.rs']+='\n'+ch
    compact=blob('crates/aspis-r1-cost-probe/src/compact.rs')
    consts=[text(n,compact) for n in P.parse(compact).root_node.named_children if n.type=='const_item' and n.child_by_field_name('name') and text(n.child_by_field_name('name'),compact)!='_']
    # Add the one referenced verifier constant exactly; no constant evaluation
    # is supplied as an unchecked literal surrogate.
    verifier=blob('crates/aspis-r1-cost-probe/src/verifier.rs')
    sem=next(text(n,verifier) for n in P.parse(verifier).root_node.named_children if n.type=='const_item' and text(n.child_by_field_name('name'),verifier)=='SEMANTIC_BYTES')
    cand=blob('crates/aspis-r1-cost-probe/src/candidate.rs')
    src='use crate::multiproof;\nmod compact {\n'+'\n'.join(consts)+'\n'+fn(compact,'slot_offset')[0]+'\n}\n'
    for qual in ['opening','slot','batch_keys']:
        body,line=fn(cand,qual);src+=body+'\n';pins['declarations'].append(dict(owner=qual,path='crates/aspis-r1-cost-probe/src/candidate.rs',line=line,original_sha256=sha(body.encode()),edit='none; exact function in isolated namespace'))
    src+='const OPENING:usize=compact::OPENING;\nstruct Reader<\'a>{bytes:&\'a[u8],at:usize}\nimpl Reader<\'_> {\n'+fn(verifier,"Reader<'a>::raw")[0]+'\n}\n'+(KIT/'layout-harnesses.rs').read_text()
    basefiles['layout.rs']=src
    basefiles['lib.rs']+='mod layout;\nmod verifier {\n'+sem+'\n}\n'
    for qual,srcpath,data in [('slot_offset','crates/aspis-r1-cost-probe/src/compact.rs',compact),("Reader<'a>::raw",'crates/aspis-r1-cost-probe/src/verifier.rs',verifier)]:
        body,line=fn(data,qual)
        pins['declarations'].append(dict(owner=qual,path=srcpath,line=line,original_sha256=sha(body.encode()),edit='none; exact frozen body; isolated namespace context'))
    pins['compact_constants']=[dict(expression=x,sha256=sha(x.encode())) for x in consts]
    pins['split_fragments']=checks
    # Verify abstract raw formulas against all four frozen source expressions.
    fast=blob('crates/aspis-r1-cost-probe/src/fast_pairing.rs');raw,_=fn(fast,'canonical::Q::raw')
    rawtree=P.parse(raw.encode());arrays=[n for n in walk(rawtree.root_node) if n.type=='array_expression']
    arr=arrays[-1]
    h=(KIT/'canonical-harnesses.rs').read_text()
    rawpins=[]
    for i,n in enumerate(arr.named_children):
        orig=text(n,raw.encode());repl=re.sub(r'([a-h])\*([a-h])',lambda x:x[1]+x[2],orig).replace('.wrapping_add(','.r22_add(').replace('.wrapping_sub(','.r22_sub(')
        repl=re.sub(r'^\((\w+)\)',r'\1',repl)
        assert normalize(repl) in normalize(h),('raw expression drift',i,repl)
        rawpins.append(dict(coordinate=i,original=orig,abstract_checked=repl,original_sha256=sha(orig.encode()),replacement='Canonical limb products replaced by independent products <=(P-1)^2; u,v <=3P. Widened multiplication safety checked separately.'))
    pins['raw_expression_correspondence']=rawpins
    for p,b in [('crates/aspis-r1-cost-probe/src/compact.rs',compact),('crates/aspis-r1-cost-probe/src/candidate.rs',cand),('crates/aspis-r1-cost-probe/src/verifier.rs',verifier)]:pins['source_files'][p]=sha(b)
    pins['generated']={k:sha(v.encode()) for k,v in basefiles.items()}
    return basefiles,pins
if __name__=='__main__':
    from prepare import build as base
    a=argparse.ArgumentParser();a.add_argument('--check',action='store_true');args=a.parse_args()
    files,pins=build(*base());files['source-pins.json']=json.dumps(pins,indent=2,sort_keys=True)+'\n'
    for name,body in files.items():
        dest=KIT/'generated'/name
        if args.check:assert dest.read_text()==body,name
        else:dest.write_text(body)
    print('extended source pins checked' if args.check else 'extended source pins generated')
