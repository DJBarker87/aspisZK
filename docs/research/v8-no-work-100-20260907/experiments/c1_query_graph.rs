//! C1-prefix adapter for V7MerkleQueryExtractor's raw-query grammar.
//! Instrumented SHA gateway access in a ROM-style experiment, NOT public
//! transcript access and NOT a Rust translation of the two-tree Lean endpoint.
use super::*;
use std::{cell::RefCell,collections::BTreeMap};
type D=[u8;26];
thread_local! {static LOG:RefCell<Option<Vec<Vec<u8>>>>=const{RefCell::new(None)};}
pub fn begin(){LOG.with(|l|{assert!(l.borrow().is_none());*l.borrow_mut()=Some(vec![])});}
pub fn record(parts:&[&[u8]]){LOG.with(|l|{if let Some(log)=l.borrow_mut().as_mut(){log.push(parts.concat());}});}
pub fn freeze()->Vec<Vec<u8>>{LOG.with(|l|l.borrow_mut().take().expect("active prefix recorder"))}
fn digest(input:&[u8])->D{let h=Sha256::digest(input);h[..26].try_into().unwrap()}
fn node(left:D,right:D)->Vec<u8>{let mut b=vec![0x11];b.extend(left);b.extend(right);b}
#[derive(Debug,PartialEq,Eq)] pub enum Failure{MissingRoot,MissingPreimage,ForwardReference,Collision,Malformed,Canonical,Fuel,Depth,RootMismatch,NotCodeword}
#[derive(Debug,Default)] pub struct Stats{pub raw_queries:usize,pub unique_queries:usize,pub raw_bytes:usize,pub walk_nodes:usize,pub default_leaves:usize,pub index_hashes:usize,pub recompute_hashes:usize}
#[derive(Clone,PartialEq,Eq)] pub struct Leaf{pub value:[u8;403],pub salt:[u8;32]}
fn default_leaf()->Leaf{Leaf{value:[0;403],salt:[0;32]}}
fn leaf_input(l:&Leaf)->Vec<u8>{let mut b=vec![0x10,0x71];b.extend(l.value);b.extend(l.salt);b}
struct Index<'a>{log:&'a[Vec<u8>],first:BTreeMap<D,usize>,defaults:Vec<D>,stats:Stats}
impl<'a> Index<'a>{
    fn new(log:&'a[Vec<u8>],depth:usize,h:fn(&[u8])->D)->Result<Self,Failure>{
        if depth>18{return Err(Failure::Depth)}
        let mut first:BTreeMap<D,usize>=BTreeMap::new();
        let mut stats=Stats{raw_queries:log.len(),raw_bytes:log.iter().map(Vec::len).sum(),..Stats::default()};
        for(i,input)in log.iter().enumerate(){let d=h(input);stats.index_hashes+=1;
            if let Some(&j)=first.get(&d){if log[j]!=*input{return Err(Failure::Collision)}}else{first.insert(d,i);}}
        stats.unique_queries=first.len();
        // All C1/C2 canonical-default inputs join the collision universe, but
        // are never inserted into the adversary's first-query index.
        let mut extras:BTreeMap<D,Vec<u8>>=BTreeMap::new();let mut defaults=vec![];
        for(tag,width)in[(0x71,403),(0xf1,186)]{let mut input=vec![0x10,tag];input.resize(2+width+32,0);
            for height in 0..=depth{let d=h(&input);stats.index_hashes+=1;
                if let Some(&j)=first.get(&d){if log[j]!=input{return Err(Failure::Collision)}}
                if let Some(old)=extras.get(&d){if *old!=input{return Err(Failure::Collision)}}
                extras.insert(d,input);if tag==0x71{defaults.push(d)}
                if height<depth{input=node(d,d)}else{break}
            }}
        Ok(Self{log,first,defaults,stats})
    }
    fn walk(&mut self,height:usize,expected:D,before:usize,root:bool,strict:bool,fuel:&mut usize,out:&mut Vec<Leaf>)->Result<(),Failure>{
        if *fuel==0{return Err(Failure::Fuel)}*fuel-=1;self.stats.walk_nodes+=1;
        if !root&&expected==self.defaults[height]{let n=1<<height;self.stats.default_leaves+=n;out.extend(std::iter::repeat_n(default_leaf(),n));return Ok(())}
        let &i=self.first.get(&expected).ok_or(if root{Failure::MissingRoot}else{Failure::MissingPreimage})?;
        if i>=before{return Err(Failure::ForwardReference)}
        let b=&self.log[i];
        if height==0{
            if b.len()!=437||b[..2]!=[0x10,0x71]{return Err(Failure::Malformed)}
            // This adapter strengthens the raw K1.2 extraction with canonical
            // M31 values for every column, not only the subsequently read ones.
            if strict{for j in 0..104{super::authenticated_c1::read31(&b[2..405],31*j).map_err(|_|Failure::Canonical)?;}}
            out.push(Leaf{value:b[2..405].try_into().unwrap(),salt:b[405..437].try_into().unwrap()});Ok(())
        }else{
            if b.len()!=53||b[0]!=0x11{return Err(Failure::Malformed)}
            let left=b[1..27].try_into().unwrap();let right=b[27..53].try_into().unwrap();
            self.walk(height-1,left,i,false,strict,fuel,out)?;self.walk(height-1,right,i,false,strict,fuel,out)
        }
    }
}
pub struct Extracted{pub leaves:Vec<Leaf>,pub tree:Vec<Vec<D>>,pub stats:Stats}
pub fn extract(log:&[Vec<u8>],root:D,depth:usize,fuel:usize)->Result<Extracted,Failure>{
    extract_mode(log,root,depth,fuel,true)
}
/// Preserve authenticated bytes. Totalization is a separate arithmetic map.
pub fn extract_raw(log:&[Vec<u8>],root:D,depth:usize,fuel:usize)->Result<Extracted,Failure>{
    extract_mode(log,root,depth,fuel,false)
}
fn extract_mode(log:&[Vec<u8>],root:D,depth:usize,mut fuel:usize,strict:bool)->Result<Extracted,Failure>{
    let mut ix=Index::new(log,depth,digest)?;let mut leaves=Vec::with_capacity(1<<depth);
    ix.walk(depth,root,log.len(),true,strict,&mut fuel,&mut leaves)?;
    if leaves.len()!=1<<depth{return Err(Failure::RootMismatch)}
    let mut tree=vec![leaves.iter().map(|l|digest(&leaf_input(l))).collect::<Vec<_>>()];
    for _ in 0..depth{tree.push(tree.last().unwrap().chunks_exact(2).map(|v|digest(&node(v[0],v[1]))).collect());}
    ix.stats.recompute_hashes=2*leaves.len()-1;
    if tree[depth][0]!=root{return Err(Failure::RootMismatch)}
    Ok(Extracted{leaves,tree,stats:ix.stats})
}
impl Extracted{
    pub fn totalized_value(&self,fibre:usize,slot:usize,col:usize)->Result<M31,Failure>{
        if fibre>=self.leaves.len()||slot>=4||col>=26{return Err(Failure::Depth)}
        // Literal Option.getD(0) convention in V7ExtractedLaneWords.c1Received.
        Ok(super::authenticated_c1::read31(&self.leaves[fibre].value,31*(slot*26+col)).unwrap_or(M31::ZERO))
    }
    pub fn candidate_at(&self,d:&super::authenticated_c1::Decoder)
        ->Result<aspis_statement::state_only_trace::StateOnlyTraceFoundation,Failure>{
        if d.first_position%4!=0||d.first_position+1024>4*self.leaves.len(){return Err(Failure::Depth)}
        let mut values=vec![vec![M31::ZERO;1024];16];
        for i in 0..1024{let pos=d.first_position+i;let leaf=&self.leaves[pos/4];
            for col in 0..16{values[col][i]=super::authenticated_c1::read31(&leaf.value,31*((pos%4)*26+col)).map_err(|_|Failure::Canonical)?;}}
        Ok(aspis_statement::state_only_trace::StateOnlyTraceFoundation{c1:std::array::from_fn(|col|d.solve_base(&values[col]))})
    }
    pub fn openings(&self)->super::authenticated_c1::C1Openings{
        assert_eq!(self.leaves.len(),1<<18);
        super::authenticated_c1::C1Openings{ids:(0..256).collect(),leaves:self.leaves[..256].iter().map(|l|l.value.to_vec()).collect(),
            salts:self.leaves[..256].iter().map(|l|l.salt).collect(),frontier:super::fixtures::frontier(&self.tree,&(0..256).collect::<Vec<_>>())}
    }
    pub fn recover_exact(&self,d:&super::authenticated_c1::Decoder,enc:&super::circle_candidate::CircleEncoder)
        ->Result<aspis_statement::state_only_trace::StateOnlyTraceFoundation,Failure>{
        let table=super::authenticated_c1::recover_c1(self.tree[18][0],&self.openings(),d).map_err(|_|Failure::Canonical)?;
        for col in 0..16{let encoded=enc.encode_c1_message(&table.c1[col]).map_err(|_|Failure::NotCodeword)?;
            for(i,leaf)in self.leaves.iter().enumerate(){for slot in 0..4{
                let value=super::authenticated_c1::read31(&leaf.value,31*(slot*26+col)).map_err(|_|Failure::Canonical)?;
                if encoded[4*i+slot]!=value{return Err(Failure::NotCodeword)}
            }}}
        Ok(table)
    }
}
pub fn controls(){
    let mut a=default_leaf();a.value[0]=1;let mut b=default_leaf();b.value[0]=2;
    let la=leaf_input(&a);let lb=leaf_input(&b);let n=node(digest(&la),digest(&lb));let root=digest(&n);
    let good=vec![la.clone(),lb.clone(),n.clone()];
    assert!(extract(&good,root,1,3).unwrap().leaves==vec![a.clone(),b.clone()]);
    assert!(matches!(extract(&good,root,1,2),Err(Failure::Fuel)));
    assert!(matches!(extract(&good[..2],root,1,3),Err(Failure::MissingRoot)));
    assert!(matches!(extract(&[lb.clone(),n.clone()],root,1,3),Err(Failure::MissingPreimage)));
    assert!(matches!(extract(&[n.clone(),la.clone(),lb.clone()],root,1,3),Err(Failure::ForwardReference)));
    let mut dup=good.clone();dup.extend(good.clone());assert_eq!(extract(&dup,root,1,3).unwrap().stats.unique_queries,3);
    let d=digest(&leaf_input(&default_leaf()));let ndef=node(digest(&la),d);
    let def=extract(&[la.clone(),ndef.clone()],digest(&ndef),1,3).unwrap();assert_eq!(def.stats.default_leaves,1);
    let wrong=vec![0x10,0xf1];assert!(matches!(extract(&[wrong.clone()],digest(&wrong),0,1),Err(Failure::Malformed)));
    let mut nc=la.clone();nc[2..5].fill(255);nc[5]|=127;assert!(matches!(extract(&[nc.clone()],digest(&nc),0,1),Err(Failure::Canonical)));
    let raw=extract_raw(&[nc.clone()],digest(&nc),0,1).unwrap();
    assert!(raw.leaves[0].value[..4]==nc[2..6]);
    assert_eq!(raw.totalized_value(0,0,0),Ok(M31::ZERO));
    assert!(super::authenticated_c1::read31(&raw.leaves[0].value,0).is_err());
    assert!(gamma_combine_v6_packed_layer0(&raw.leaves[0].value,&[0;186],&StateOnlySpendQueryPowers::new(K::ONE)).is_err());
    assert!(matches!(raw.totalized_value(0,4,0),Err(Failure::Depth)));
    println!("raw_totalization_controls=5 authenticated_bytes_preserved=true selected_gamma_parser_still_rejects=true");
    assert!(matches!(Index::new(&[vec![1],vec![2]],1,|_|[0;26]),Err(Failure::Collision)));
    // Missing at the frozen prefix is not repaired by post-prefix queries.
    let prefix=vec![lb,n.clone()];assert!(extract(&prefix,root,1,3).is_err());
    let mut late=prefix.clone();late.push(la);assert!(matches!(extract(&late,root,1,3),Err(Failure::ForwardReference)));
    assert!(extract(&prefix,root,1,3).is_err());
    println!("graph_controls=11 passed=true future_queries_do_not_repair_prefix=true");
}
pub fn outside_sample_control(log:&[Vec<u8>],ex:&Extracted,d:&super::authenticated_c1::Decoder,enc:&super::circle_candidate::CircleEncoder){
    // New committed word: mutate fibre 256, outside the 0..255 interpolation
    // system. Rehash only its path, with all siblings already in the log.
    let mut changed=log.to_vec();let mut leaf=ex.leaves[256].clone();leaf.value[0]^=1;
    let input=leaf_input(&leaf);let mut acc=digest(&input);changed.push(input);let mut id=256;
    for level in 0..18{let sibling=ex.tree[level][id^1];let input=if id%2==0{node(acc,sibling)}else{node(sibling,acc)};
        acc=digest(&input);changed.push(input);id>>=1;}
    let recovered=extract(&changed,acc,18,(1<<19)-1).unwrap();
    let a=super::authenticated_c1::recover_c1(acc,&recovered.openings(),d).unwrap();
    let b=super::authenticated_c1::recover_c1(ex.tree[18][0],&ex.openings(),d).unwrap();assert_eq!(a,b);
    assert!(matches!(recovered.recover_exact(d,enc),Err(Failure::NotCodeword)));
    println!("outside_sample_C1_change authenticated=true sample_coefficients_unchanged=true full_word_rejected=true");
}

pub fn exhaustive_depth_two_query_orders(){
    controls();
    let mut queries=Vec::new();
    for i in 1..=4{let mut l=default_leaf();l.value[0]=i;queries.push(leaf_input(&l));}
    queries.push(node(digest(&queries[0]),digest(&queries[1])));
    queries.push(node(digest(&queries[2]),digest(&queries[3])));
    queries.push(node(digest(&queries[4]),digest(&queries[5])));
    let root=digest(&queries[6]);let mut permutations=0;let mut success=0;
    fn visit(ids:&mut[usize;7],k:usize,queries:&[Vec<u8>],root:D,count:&mut usize,success:&mut usize){
        if k==7{
            let mut where_is=[0;7];for(i,&id)in ids.iter().enumerate(){where_is[id]=i;}
            let causal=[(0,4),(1,4),(2,5),(3,5),(4,6),(5,6)].iter().all(|&(c,p)|where_is[c]<where_is[p]);
            let log=ids.iter().map(|&i|queries[i].clone()).collect::<Vec<_>>();
            let actual=extract(&log,root,2,7).is_ok();assert_eq!(actual,causal);
            *count+=1;*success+=actual as usize;return
        }
        for i in k..7{ids.swap(k,i);visit(ids,k+1,queries,root,count,success);ids.swap(k,i);}
    }
    visit(&mut[0,1,2,3,4,5,6],0,&queries,root,&mut permutations,&mut success);
    assert_eq!((permutations,success),(5040,80));
    println!("all_query_orders=5040 causal_successes=80 others_rejected=4960");
}
