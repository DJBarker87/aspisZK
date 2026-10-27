"""Prepare prover-only fixed-carrier copies; never modify statement sources."""
from pathlib import Path
R=Path.cwd(); S=R/'crates/aspis-statement/src/pool_v1'; D=R/'crates/aspis-r1-cost-probe/src'
def section(s,a,b):return s[s.index(a):s.index(b,s.index(a))]
h=(S/'pair_tree_hiding.rs').read_text();f=(S/'pair_forest_hiding.rs').read_text();t=(S/'pair_trace.rs').read_text();ft=(S/'pair_forest_trace.rs').read_text()
header='''//! Prover-local Drop-free forest inventory. Originals remain in aspis-statement.
use aspis_statement::pool_v1::{pair_tree_hiding::*, pair_tree_profile::*, pair_forest_hiding::*};
use aspis_statement::pool_v1::pair_trace::*;
use aspis_statement::trace_v4::TraceCell;
use aspis_statement::poseidon2::MERKLE_NODE_COMPRESSION_V3_TWEAK;
use aspis_core::field::{M31, QM31};
use alloc::{vec,vec::Vec};
use aspis_statement::logup::{CopyLogUpRow,compress_tagged_tuple,build_copy_logup_helper};
use aspis_statement::pool_v1::pair_forest_trace::PoolV1PairForestTraceV1;

#[derive(Clone,Copy)]
pub struct Schedule { pub data:[PoolV1PairCopyRowLinkV1;136], pub len:usize }
impl Schedule {
 fn new()->Self {Self {data:[PoolV1PairCopyRowLinkV1 {kind:PoolV1PairCopyRowLinkKindV1::OwnerOutput,producer_row:0,consumer_row:0};136],len:0}}
 fn push(&mut self,value:PoolV1PairCopyRowLinkV1){self.data[self.len]=value;self.len+=1;}
 fn len(&self)->usize {self.len}
}
#[derive(Clone,Copy)]
pub struct Registry { pub data:[PoolV1PairCopyLinkV1;136], pub len:usize }
impl Registry {
 fn new()->Self { Self {data:[PoolV1PairCopyLinkV1 {id:0,tag:M31::ZERO,kind:PoolV1PairCopyRowLinkKindV1::OwnerOutput,weight:PoolV1PairCopyWeightV1::One,producer:PoolV1PairCopyTupleV1{row:0,limbs:[PoolV1PairTupleLimbV1::Zero;16]},consumer:PoolV1PairCopyTupleV1{row:0,limbs:[PoolV1PairTupleLimbV1::Zero;16]}};136],len:0} }
 fn push(&mut self,value:PoolV1PairCopyLinkV1){self.data[self.len]=value;self.len+=1;}
 fn len(&self)->usize {self.len}
}
'''
link=section(h,'#[inline]\nfn link(','/// Exact row endpoints')
legacy=section(h,'pub fn build_pool_v1_pair_copy_row_schedule_v1(','\nfn endpoint_counts(')
legacy=legacy.replace('Result<Vec<PoolV1PairCopyRowLinkV1>', 'Result<Schedule').replace('Vec::with_capacity(POOL_V1_PAIR_COPY_ROW_LINKS_V1)','Schedule::new()').replace('endpoint_counts(&links)?','endpoint_counts(&links.data[..links.len])?')
# Replace iterator loops by index loops, keeping body statements and order.
def loop(src,start,end,init,head,tail):
 a=src.index(start); b=src.index(end,a)+len(end); part=src[a:b]; body=part[part.index('{')+1:part.rfind('}')]; return src[:a]+init+head+body+tail+src[b:]
a=legacy.index('    for (from, to) in [');b=legacy.index('    links.push(link(PoolV1PairCopyRowLinkKindV1::OwnerOutput',a)
chunk=legacy[a:b]; head,body=chunk.split('] {',1);body=body[:body.rfind('}')]
legacy=legacy[:a]+head.replace('    for (from, to) in [','    let pairs = [')+']; let mut pi=0usize; while pi<7 { let (from,to)=pairs[pi];'+body+'pi+=1; }\n'+legacy[b:]
# Generic range loops in these exact constructors, brace matching.
def ranges(src):
 import re
 while m:=re.search(r'for (\w+) in 0\.\.([^\{\n]+)\{',src):
  a=m.start();i=m.end();depth=1;j=i
  while depth:
   if src[j]=='{':depth+=1
   if src[j]=='}':depth-=1
   j+=1
  name,bound=m.group(1),m.group(2).strip();src=src[:a]+f'let mut {name}=0usize; while {name}<{bound} {{'+src[i:j-1]+f'{name}+=1; }}'+src[j:]
 return src
legacy=ranges(legacy)
a=legacy.index('    for (value, source_row, destination_row) in');b=legacy.index('    links.push(link(\n        PoolV1PairCopyRowLinkKindV1::ConservationInput',a)
chunk=legacy[a:b];_,body=chunk.split('    {',1);body=body[:body.rfind('}')]
legacy=legacy[:a]+'    let values=[(0u8,44usize,960usize),(1,460,962),(2,508,964)]; let mut vi=0usize; while vi<3 {let (value,source_row,destination_row)=values[vi];'+body+'vi+=1;}\n'+legacy[b:]
endpoint='''fn endpoint_counts(links:&[PoolV1PairCopyRowLinkV1])->Result<([u8;1024],[u8;1024]),PoolV1PairHidingLayoutErrorV1>{
 let mut producers=[0u8;1024];let mut consumers=[0u8;1024];let mut i=0usize;
 while i<links.len(){let item=links[i];let p=item.producer_row as usize;let c=item.consumer_row as usize;
 if p>=1024 || producers[p]>=2{return Err(PoolV1PairHidingLayoutErrorV1::EndpointCapacity{row:p as u16});}producers[p]+=1;
 if c>=1024 || consumers[c]>=2{return Err(PoolV1PairHidingLayoutErrorV1::EndpointCapacity{row:c as u16});}consumers[c]+=1;i+=1;}
 Ok((producers,consumers))
}
'''
forest=section(f,'pub fn build_pool_v1_pair_forest_copy_row_schedule_v1(','\npub fn pool_v1_pair_forest_copy_active_rows_v1')
a=forest.index('    let mut links =');b=forest.index('    // The existing schedule',a)
forest=forest[:a]+'''    let legacy=build_pool_v1_pair_copy_row_schedule_v1()?;
    let mut links=Schedule::new();let mut i=0usize;
    while i<legacy.len {let scheduled=legacy.data[i];if !matches!(scheduled.kind,PoolV1PairCopyRowLinkKindV1::PrivatePathCurrent{..}|PoolV1PairCopyRowLinkKindV1::PrivatePathLeft{..}|PoolV1PairCopyRowLinkKindV1::PrivatePathRight{..}){links.push(scheduled);}i+=1;}
'''+forest[b:]
forest=forest.replace('Result<Vec<PoolV1PairCopyRowLinkV1>', 'Result<Schedule').replace('for scheduled in &mut links {','let mut si=0usize; while si<links.len {let mut scheduled=links.data[si];').replace('    links.reserve(3 * POOL_V1_PAIR_FOREST_PRIVATE_DIRECTIONS_V1);','')
forest=forest.replace('    }\n\n    for level','        links.data[si]=scheduled;si+=1;\n    }\n\n    for level') if '    }\n\n    for level' in forest else forest.replace('    }\n\n    \n    for level','        links.data[si]=scheduled;si+=1;\n    }\n\n    for level')
# Avoid reliance on blank-line matching for the loop's closing brace.
if 'links.data[si]=scheduled' not in forest:
 needle='scheduled.consumer_row += 3 * POOL_V1_PAIR_TRACE_BLOCK_ROWS as u16;\n        }\n    }'
 assert needle in forest
 forest=forest.replace(needle,needle[:-5]+'        links.data[si]=scheduled;si+=1;\n    }')
forest=ranges(forest).replace('endpoint_counts(&links)?','endpoint_counts(&links.data[..links.len])?')
active='''pub fn pool_v1_pair_forest_copy_active_rows_v1()->Result<([u16;214],usize),PoolV1PairHidingLayoutErrorV1>{
 let schedule=build_pool_v1_pair_forest_copy_row_schedule_v1()?;let mut flags=[false;1024];let mut i=0usize;
 while i<schedule.len {let link=schedule.data[i];flags[link.producer_row as usize]=true;flags[link.consumer_row as usize]=true;i+=1;}
 let mut rows=[0u16;214];let mut len=0usize;i=0;while i<1024{if flags[i]{rows[len]=i as u16;len+=1;}i+=1;}Ok((rows,len))
}
pub fn pool_v1_pair_forest_copy_active_row_masks_v1()->Result<[u16;64],PoolV1PairHidingLayoutErrorV1>{
 let (rows,len)=pool_v1_pair_forest_copy_active_rows_v1()?;let mut masks=[0u16;64];let mut i=0usize;while i<len{let row=rows[i] as usize;masks[row>>4u32]|=1u16<<((row&15) as u32);i+=1;}Ok(masks)
}
pub fn pool_v1_pair_forest_copy_inactive_row_masks_v1()->Result<[u16;64],PoolV1PairHidingLayoutErrorV1>{
 let mut masks=pool_v1_pair_forest_copy_active_row_masks_v1()?;let mut i=0usize;while i<64{masks[i]=!masks[i];i+=1;}Ok(masks)
}
'''
tuples=ranges(section(t,'fn bank_for_row(', '\npub fn build_pool_v1_pair_copy_registry_v1('))
reg=section(t,'pub fn build_pool_v1_pair_copy_registry_v1(', '\nfn tuple_value(')
reg=reg.replace('Result<Vec<PoolV1PairCopyLinkV1>','Result<Registry').replace('Vec::with_capacity(rows.len())','Registry::new()').replace('    for scheduled in rows {','    let mut ri=0usize;while ri<rows.len {let scheduled=rows.data[ri];').replace('    }\n    if output.len()', '        ri+=1;\n    }\n    if output.len()')
translate=section(ft,'fn translate_aux_tuple(', '\npub fn build_pool_v1_pair_forest_copy_registry_v1(')
a=translate.index('    for limb in &mut tuple.limbs {');b=translate.index('    tuple\n',a)
translate=translate[:a]+'''    let mut i=0usize;while i<16{if let PoolV1PairTupleLimbV1::Cell{mut source,offset}=tuple.limbs[i]{if source.cell.row>=864{source.cell.row+=48;}tuple.limbs[i]=PoolV1PairTupleLimbV1::Cell{source,offset};}i+=1;}
'''+translate[b:]
fr=section(ft,'pub fn build_pool_v1_pair_forest_copy_registry_v1(', '\nfn tuple_value(')
fr=fr.replace('Result<Vec<PoolV1PairCopyLinkV1>','Result<Registry').replace('Vec::with_capacity(schedule.len())','Registry::new()').replace('    for scheduled in schedule {','    let mut si=0usize;while si<schedule.len {let scheduled=schedule.data[si];').replace('    }\n    if output.len()', '        si+=1;\n    }\n    if output.len()')
a=fr.index('            let old = legacy');b=fr.index('            (\n                translate_aux_tuple',a)
fr=fr[:a]+'''            let mut found=None;let mut i=0usize;while i<legacy.len && found.is_none(){if legacy.data[i].kind==scheduled.kind{found=Some(legacy.data[i]);}i+=1;}
            let old=match found{Some(value)=>value,None=>return Err(PoolV1PairTraceErrorV1::CopyLayout)};
'''+fr[b:]
# The copied caller returns the same Vec carrier; only registry/schedule become fixed arrays.
rows=section(ft,'fn tuple_value(', '\npub fn verify_pool_v1_pair_forest_copy_registry_v1(')
rows=rows.replace('    for link in build_pool_v1_pair_forest_copy_registry_v1()? {','    let registry=build_pool_v1_pair_forest_copy_registry_v1()?;let mut i=0usize;while i<registry.len {let link=registry.data[i];').replace('    Ok(rows)','    Ok(rows)')
pos=rows.rindex('    }\n    Ok(rows)');rows=rows[:pos]+'        i+=1;\n'+rows[pos:]
helper=section((S/'pair_forest_semantic_oracle.rs').read_text(),'pub fn build_pool_v1_pair_forest_copy_helper_v1(', '\n/// Evaluate the exact forest copy lane')
(D/'host_forest.rs').write_text(header+link+legacy+endpoint+forest+active+tuples+reg+translate+fr+rows+'\n'+helper)
lib=D/'lib.rs';s=lib.read_text();s+='\n#[cfg(feature = "prover")]\npub mod host_forest;\n';lib.write_text(s)
p=D/'host_semantic.rs';s=p.read_text().replace('pair_forest_semantic_oracle::build_pool_v1_pair_forest_copy_helper_v1,','');s=s.replace('use alloc::vec::Vec;','use alloc::vec::Vec;\nuse crate::host_forest::build_pool_v1_pair_forest_copy_helper_v1;');s=s.replace('aspis_statement::pool_v1::pool_v1_pair_forest_copy_active_row_masks_v1()', 'crate::host_forest::pool_v1_pair_forest_copy_active_row_masks_v1()');s=s.replace('aspis_statement::pool_v1::pair_forest_trace::build_pool_v1_pair_forest_copy_registry_v1()', 'crate::host_forest::build_pool_v1_pair_forest_copy_registry_v1()');s=s.replace('let count=registry.len();let mut index=0;', 'let count=registry.len;let mut index=0;').replace('let link=registry[index];','let link=registry.data[index];');p.write_text(s)
