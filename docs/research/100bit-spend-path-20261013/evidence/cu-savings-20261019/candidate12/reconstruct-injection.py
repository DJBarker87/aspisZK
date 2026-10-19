from pathlib import Path
w=Path('/home/dombarker/project-offloads/aspis-r1-cu-savings-20261019');p=w/'injections/crates/aspis-r1-cost-probe/src/verifier.rs';old=p.read_text();marker='#[cfg(all(test,feature="private-leaf-salts"))]\npub fn migration_old_tx1';extra=old[old.index(marker):]
# The current production prefix already includes the new focused test module.
if 'mod batched_weight_tests' in extra:
 start=extra.rfind('#[cfg(test)]',0,extra.index('mod batched_weight_tests'));a=extra.index('{',extra.index('mod batched_weight_tests'));end=a+1;depth=1
 while depth:depth+=(extra[end]=='{')-(extra[end]=='}');end+=1
 extra=extra[:start]+extra[end:]
s=(w/'verifier.rs').read_text()
for anchor,hook in [('pub fn new<H:Digest32>(sem:', 'if decision1h_migration_tests::before_prepare(){return Err(Error::Transcript)}'),('fn for_range(queries:', 'if decision1h_migration_tests::before_geometry(queries,start,end){return Err(Error::Query)}'),('fn query_with_geometry<H:', '{if let Some(weights)=pending.as_ref(){weights.finish(&mut a.weights);}if decision1h_migration_tests::before_query(p,a){return Err(Error::Query)}}')]:
 a=s.index('{',s.index(anchor))+1;s=s[:a]+'\n#[cfg(all(test,feature="private-leaf-salts"))] '+hook+s[a:]
s=s.replace('let bytes=checkpoint(&p,&a,proof,public_bytes,hash);','let bytes={ #[cfg(all(test,feature="private-leaf-salts"))] { crate::verifier::decision1h_migration_tests::checkpoint_result(&p,&a,proof,public_bytes,hash)? } #[cfg(not(all(test,feature="private-leaf-salts")))] { checkpoint(&p,&a,proof,public_bytes,hash) } };',1)
s=s.replace('let sem=crate::r1_semantic::verify_observed(public,v.semantic,hash,obs).map_err(|_|Error::Semantic)?;','let sem={ #[cfg(all(test,feature="private-leaf-salts"))] { crate::verifier::decision1h_migration_tests::semantic(public,v.semantic,hash,obs)? } #[cfg(not(all(test,feature="private-leaf-salts")))] { crate::r1_semantic::verify_observed(public,v.semantic,hash,obs).map_err(|_|Error::Semantic)? } };',1)
p.write_text(s+'\n'+extra)
