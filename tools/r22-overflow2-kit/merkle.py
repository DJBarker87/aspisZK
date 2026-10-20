"""Composable source-bound validator and parent-group contracts."""
def build(get,blob,fn,pins,sha):
    M='crates/aspis-r1-cost-probe/src/multiproof.rs'
    s='''const MAX_BATCH:usize=16;const LEAF_BITS:u32=18;
#[derive(Clone,Copy,kani::Arbitrary)] enum Arity{Two,Eight}
impl Arity {
'''
    for q in ['bits','width','levels']:s+=get(M,'Arity::'+q)
    s+='}\n'
    suffix=' && '.join(f'({k}<i || {k}>=n || (a[{k}]<(1<<18)'+(f' && ({k}==i || a[{k-1}]<a[{k}])' if k else '')+'))' for k in range(16))
    s+='fn sorted_suffix(a:&[u32;16],i:usize,n:usize)->bool {'+suffix+'}\n'
    ordered=' && '.join(f'({k}>=indices.len() || (indices[{k}]<(1<<18)'+(f' && indices[{k-1}]<indices[{k}]' if k else '')+'))' for k in range(16))
    s+=get(M,'well_formed','#[kani::requires(indices.len()<=16)]\n#[kani::ensures(|r:&bool| !*r || (!indices.is_empty() && '+ordered+'))]')
    s+=get(M,'index_at')
    s+='''#[kani::proof_for_contract(well_formed)] #[kani::unwind(18)]
fn validator() {let a:[u32;16]=kani::any();let n:usize=kani::any();kani::assume(n<=16);well_formed(&a[..n]);}
'''
    body=fn(blob(M),'node_count')[0]
    fragment='''let parent = index_at(&level, i) >> arity.bits();
            let mut j = i;
            while j < n && index_at(&level, j) >> arity.bits() == parent {
                j += 1;
            }'''
    assert fragment in body
    s+='''#[kani::requires(n<=16 && i<n && sorted_suffix(&level,i,n))]
#[kani::ensures(|j:&usize| i<*j && *j<=n && *j-i<=arity.width() && (*j==n || index_at(&level,*j)>>arity.bits()>index_at(&level,i)>>arity.bits()))]
fn group_end(arity:Arity,level:[u32;16],i:usize,n:usize)->usize {
'''+fragment+'\nj\n}\n'
    pins.append(dict(path=M,owner='node_count::parent_group',sha256=sha(fragment.encode()),body_edit='exact inner scan lifted into group_end; returns j; suffix-only sorted invariant ignores overwritten prefix and dead gap'))
    s+='''#[kani::proof_for_contract(group_end)] #[kani::unwind(18)]
fn suffix_group() {group_end(kani::any(),kani::any(),kani::any(),kani::any());}
#[kani::proof] #[kani::unwind(18)]
#[kani::stub_verified(well_formed)] #[kani::stub_verified(group_end)]
fn validated_group_caller(){
    let mut a:[u32;16]=kani::any();let n:usize=kani::any();kani::assume(n<=16);
    if !well_formed(&a[..n]) {return;}
    let i:usize=kani::any();kani::assume(i<n);
    let w:usize=kani::any();kani::assume(w<=i);
    let arity:Arity=kani::any();
    let j=group_end(arity,a,i,n);
    let siblings=arity.width()-(j-i);
    a[w]=index_at(&a,i)>>arity.bits();
    assert!(siblings<=7 && w+1<=j && j<=n);
}
'''
    return s
