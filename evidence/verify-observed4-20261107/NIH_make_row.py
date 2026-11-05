from pathlib import Path
import subprocess,json,hashlib
E=Path(__file__).resolve().parent;rev='4bb3b3f51e16b4525f1d10336e2b0bcbbd775387';path='crates/aspis-statement/src/pool_v1/pair_forest_copy_terminal.rs'
src=subprocess.check_output(['git','show',rev+':'+path],text=True)
original=src[src.index('    pub(crate) fn row(&self, row: usize) -> QM31 {'):];original=original[:original.index('\n    }')+6]
body=original.replace('    pub(crate) fn row(&self, row: usize)', '    fn NIH_row(selectors:&Selectors, row: usize,log:&mut NIH_ProductLog)').replace('self.high[row >> 4].mul(self.low[row & 15])','NIH_product(selectors.high[row >> 4],selectors.low[row & 15],log)')
assert body.replace('    fn NIH_row(selectors:&Selectors, row: usize,log:&mut NIH_ProductLog)','    pub(crate) fn row(&self, row: usize)').replace('NIH_product(selectors.high[row >> 4],selectors.low[row & 15],log)','self.high[row >> 4].mul(self.low[row & 15])')==original
s='''
struct NIH_ProductLog{left:[u32;4],right:[u32;4],reply:[u32;4],calls:usize}
fn NIH_canon(q:QM31)->bool{let w=NIH_words(q);w[0]<2147483647&&w[1]<2147483647&&w[2]<2147483647&&w[3]<2147483647}
fn NIH_product(left:QM31,right:QM31,log:&mut NIH_ProductLog)->QM31{
 assert!(NIH_canon(left)&&NIH_canon(right));assert_eq!(log.calls,0);
 log.left=NIH_words(left);log.right=NIH_words(right);log.calls+=1;NIH_q(log.reply)
}
'''+body+'''
#[kani::proof]#[kani::unwind(81)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn NIH_selector_row(){
 let high:[[u32;4];64]=kani::any();let low:[[u32;4];16]=kani::any();let row:usize=kani::any();kani::assume(row<1024);
 let h=high[row/16];let l=low[row%16];let reply:[u32;4]=kani::any();
 kani::assume(h[0]<2147483647&&h[1]<2147483647&&h[2]<2147483647&&h[3]<2147483647);
 kani::assume(l[0]<2147483647&&l[1]<2147483647&&l[2]<2147483647&&l[3]<2147483647);
 kani::assume(reply[0]<2147483647&&reply[1]<2147483647&&reply[2]<2147483647&&reply[3]<2147483647);
 let selectors=Selectors{high:high.map(NIH_q),low:low.map(NIH_q)};
 let mut log=NIH_ProductLog{left:kani::any(),right:kani::any(),reply,calls:0};
 let out=NIH_words(NIH_row(&selectors,row,&mut log));let j:usize=kani::any();kani::assume(j<4);
 assert_eq!(log.calls,1);assert_eq!(log.left[j],h[j]);assert_eq!(log.right[j],l[j]);assert_eq!(log.reply[j],reply[j]);
 assert_eq!(out[j],reply[j] ^ if cfg!(NIH_invert){1}else{0});
}
'''
p=E/'NIH_copy.rs.txt';assert 'fn NIH_selector_row'not in p.read_text();p.write_text(p.read_text()+s)
(E/'NIH_ROW_ERASURE.json').write_text(json.dumps(dict(revision=rev,path=path,original=original,cut=body,reverse_erasure=True,modifies='only local product log left/right/calls; reply and borrowed selectors unchanged',field_stub='NIH_product',paired_laws=['JFy_FieldTotal.mul','JFv_RawExtractedSemanticCallOpsV20.generated_qm_mul_eq_probe'],domain='selected high/low canonical; row<1024; every other input cell arbitrary'),indent=2)+'\n')
