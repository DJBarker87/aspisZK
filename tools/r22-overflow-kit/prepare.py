#!/usr/bin/env python3
"""Generate an isolated Kani crate from frozen source, with audited edits.
All methods not selected stay unreachable. Explicit wrapping arithmetic is
changed to checked operations solely in this tool crate, never shipped files.
"""
import argparse, hashlib, json, sys
from pathlib import Path
sys.path.insert(0,str(Path(__file__).resolve().parent))
from inventory import ROOT,OUT,FREEZE,blob,walk,text,owner
from tree_sitter import Language,Parser
import tree_sitter_rust
KIT=Path(__file__).resolve().parent
P=Parser(Language(tree_sitter_rust.language()))
def sha(x): return hashlib.sha256(x).hexdigest()
def fn(b,qual):
    matches=[n for n in walk(P.parse(b).root_node) if n.type=='function_item' and owner(n,b)==qual]
    assert len(matches)==1,(qual,len(matches))
    n=matches[0];return b[n.start_byte:n.end_byte].decode(),n.start_point.row+1

def build():
    p='crates/aspis-r1-cost-probe/src/fast_pairing.rs';b=blob(p)
    canonical=next(n for n in P.parse(b).root_node.named_children if n.type=='mod_item')
    source=text(canonical,b)
    # The only external-type method is not called by these harnesses.
    wide,_=fn(b,'canonical::Q::from_wide');assert source.count(wide)==1
    instrumented=source.replace(wide,'// from_wide excluded: external WideExact constructor boundary')
    instrumented=instrumented.replace('.wrapping_add(','.r22_add(').replace('.wrapping_sub(','.r22_sub(')
    # Include checked instrumentation inside canonical to resolve method traits.
    instrumented=instrumented[:-1]+(KIT/'canonical-harnesses.rs').read_text()+'\n}\n'
    files={'canonical.rs':instrumented}
    # Exact node_count control body, with a checked one-level source slice in
    # the next stage. Keep digest and SDK dependencies out of this leaf crate.
    m=blob('crates/aspis-r1-cost-probe/src/multiproof.rs')
    selected=['Arity::bits','Arity::width','Arity::levels','well_formed','index_at','node_count','sort_dedup']
    manifest=[]
    for q in ['canonical::reduce','canonical::add','canonical::pair','canonical::reduce_pair','canonical::Q::add','canonical::Q::sub','canonical::Q::half','canonical::Q::half_pow']:
        s,line=fn(b,q);manifest.append(dict(owner=q,path=p,line=line,original_sha256=sha(s.encode()),edit='wrapping_add/sub renamed to r22_add/sub; checked_*().expect assertion; no other body edits'))
    bodies={q:fn(m,q)[0] for q in selected}
    files['multiproof.rs']='pub const MAX_BATCH:usize=16; const LEAF_BITS:u32=18;\n#[derive(Clone,Copy)] enum Arity {Two,Eight}\nimpl Arity {\n'+'\n'.join(bodies[q] for q in selected[:3])+'\n}\n'+'\n'.join(bodies[q] for q in selected[3:])+'\n'+(KIT/'multiproof-harnesses.rs').read_text()
    for q in selected:
        s,line=fn(m,q);manifest.append(dict(owner=q,path='crates/aspis-r1-cost-probe/src/multiproof.rs',line=line,original_sha256=sha(s.encode()),edit='none; declaration copied verbatim; namespace/import context only'))
    files['lib.rs']='#![allow(dead_code)]\nmod canonical;\nmod multiproof;\n'
    files['Cargo.toml']='[package]\nname="r22-overflow-leaves"\nversion="0.1.0"\nedition="2021"\n[lib]\npath="lib.rs"\n[workspace]\n[profile.dev]\noverflow-checks=true\nopt-level=3\ndebug=false\n[profile.release]\noverflow-checks=true\nopt-level=3\n'
    proofpins={'source_revision':FREEZE,'source_files':{p:sha(b),'crates/aspis-r1-cost-probe/src/multiproof.rs':sha(m)},'declarations':manifest,'generated':{k:sha(v.encode()) for k,v in files.items()},'scope':'Local checked-arithmetic leaf proofs, not accepted-run source-cone composition. Raw formula harnesses use independent bounded product overapproximation and existing Lean raw_ranges, not a replay of Q::mul.'}
    return files,proofpins
if __name__=='__main__':
    a=argparse.ArgumentParser();a.add_argument('--check',action='store_true');args=a.parse_args()
    files,pins=build();dest=KIT/'generated'
    files['source-pins.json']=json.dumps(pins,indent=2,sort_keys=True)+'\n'
    for name,body in files.items():
        path=dest/name
        if args.check: assert path.read_text()==body, 'drift: '+name
        else: path.parent.mkdir(parents=True,exist_ok=True);path.write_text(body)
    print(json.dumps({'files':len(files),'source_revision':FREEZE}))
