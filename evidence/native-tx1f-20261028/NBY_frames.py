import NBY_generate as g
# Extracted binary row is identical to the first version. Only observers split.
g.text='''use super::*;
use core::cell::Cell;
#[derive(Clone,Copy)]struct Port<'a>{left:*const u8,right:*const u8,reply:&'a[u8;32],calls:&'a Cell<usize>}
impl Digest32 for Port<'_>{fn digest(&self,p:&[&[u8]])->[u8;32]{assert_eq!(p.len(),3);assert_eq!(p[0],&[BINARY_NODE_TAG]);assert_eq!(p[1].len(),32);assert_eq!(p[2].len(),32);assert_eq!(p[1].as_ptr(),self.left);assert_eq!(p[2].as_ptr(),self.right);self.calls.set(self.calls.get()+1);*self.reply}}
fn row<H:Digest32>(hash:H,idx:&mut[u32;16],val:&mut[[u8;32];16],n:usize,nodes:&[u8],mut at:usize,mut w:usize,mut i:usize)->(bool,usize,usize,usize){let parent=index_at(idx,i)>>Arity::Two.bits();let digest=if i+1<n&&index_at(idx,i+1)==index_at(idx,i)^1{let d=occupied_binary_parent(hash,val,i);i+=2;d}else{let Some(sibling)=nodes.get(at..at+32)else{return(false,at,w,i)};at+=32;let d=sibling_binary_parent(hash,val,i,sibling,index_at(idx,i)&1==0);i+=1;d};idx[w]=parent;val[w]=digest;w+=1;(true,at,w,i)}
'''
common='''let mut idx:[u32;16]=kani::any();let mut val:[[u8;32];16]=kani::any();let n:usize=kani::any();let i:usize=kani::any();let w:usize=kani::any();let k:usize=kani::any();let c:usize=kani::any();let at:usize=kani::any();let prior:usize=kani::any();kani::assume(i<n&&n<=16&&w<=i&&k<16&&c<32&&at<=5504&&prior<1000);let reply:[u8;32]=kani::any();let old_idx=idx[k];let old_val=val[k][c];let parent=idx[i]/2;let calls=Cell::new(prior);'''
for branch in ['pair','supplied']:
 for effect in ['inside','outside']:
  body=common
  if branch=='pair':
   body+='''kani::assume(i+1<n&&idx[i+1]==idx[i]^1);let hash=Port{left:val[i].as_ptr(),right:val[i+1].as_ptr(),reply:&reply,calls:&calls};'''
   args='&[],at,w,i';expected='(true,at,w+1,i+2)'
  else:
   body+='''kani::assume(!(i+1<n&&idx[i+1]==idx[i]^1));let nodes:[u8;5504]=kani::any();let length:usize=kani::any();kani::assume(length<=5504&&at+32<=length);let left=idx[i]&1==0;let selected=&nodes[at..at+32];let hash=Port{left:if left{val[i].as_ptr()}else{selected.as_ptr()},right:if left{selected.as_ptr()}else{val[i].as_ptr()},reply:&reply,calls:&calls};'''
   args='&nodes[..length],at,w,i';expected='(true,at+32,w+1,i+1)'
  body+=f'kani::assume(k{"==" if effect=="inside" else "!="}w);let out=row(hash,&mut idx,&mut val,n,{args});'
  expression=f'out=={expected}&&calls.get()==prior+1&&idx[k]=='+('parent&&val[k][c]==reply[c]' if effect=='inside' else 'old_idx&&val[k][c]==old_val')
  g.pair(branch+'_'+effect,body,expression)
body=common+'''kani::assume(!(i+1<n&&idx[i+1]==idx[i]^1));let nodes:[u8;5504]=kani::any();let len:usize=kani::any();kani::assume(len<=5504&&len<at+32);let hash=Port{left:val[i].as_ptr(),right:nodes.as_ptr(),reply:&reply,calls:&calls};let out=row(hash,&mut idx,&mut val,n,&nodes[..len],at,w,i);'''
g.pair('short_whole_frame',body,'out==(false,at,w,i)&&calls.get()==prior&&idx[k]==old_idx&&val[k][c]==old_val')
# Supply request load uses the full carrier, one arbitrary byte in selected window.
body='''let nodes:[u8;96]=kani::any();let at:usize=kani::any();let c:usize=kani::any();let k:usize=kani::any();kani::assume(at<=64&&c<32&&k<96);let old=nodes[k];let selected=nodes.get(at..at+32).unwrap();let x=selected[c];'''
g.pair('supplied_window_load',body,'x==nodes[at+c]&&nodes[k]==old&&selected.len()==32&&selected.as_ptr()==nodes.as_ptr().wrapping_add(at)')
if __name__=='__main__':g.publish('NBY_frames','multiproof.rs',17)
