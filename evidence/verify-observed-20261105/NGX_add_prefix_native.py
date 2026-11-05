from pathlib import Path
import subprocess,re,json,hashlib
E=Path(__file__).resolve().parent;p=E/'NGX_native.rs.txt';s=p.read_text();assert 'fn prefix_control' not in s
frozen=subprocess.check_output(['git','show','4bb3b3f51e16b4525f1d10336e2b0bcbbd775387:crates/aspis-r1-cost-probe/src/r1_wire.rs'],text=True)
start=frozen.index("pub fn parse(bytes: &'a [u8])");at=frozen.index('{',start);depth=1;i=at+1
while depth:depth+=(frozen[i]=='{')-(frozen[i]=='}');i+=1
original=frozen[start:i];body=frozen[at:i]
cut,count=re.subn(r'parse_record_at\(bytes, (\d+), (32|offset)\)',r'prefix_at_cut(bytes, \1, \2, log)',body);assert count==27
cut=cut.replace('Ok(Self {','Ok(Prefix {')
widths=[5+(32 if i in [2,14] else 896 if 15<=i<=24 else 3712 if i==25 else 928 if i==26 else 0) for i in range(27)];starts=[];offset=32
for width in widths:starts.append(offset);offset+=width
assert offset==13831
s+='''
struct PrefixLog {calls:usize,fail_at:usize,error:Error,rows:[u8;27],offsets:[usize;27],lengths:[usize;27]}
fn prefix_at_cut<'a>(bytes:&'a[u8],row:u8,offset:usize,log:&mut PrefixLog)->Result<(&'a[u8],usize),Error> {
 let call=log.calls;assert!(call<27);log.calls+=1;log.rows[call]=row;log.offsets[call]=offset;
 assert!(row<=26&&offset<=57607&&bytes.len()<=57607);
 let length=5+row_shape(row).unwrap().1;log.lengths[call]=length;let end=offset+length;
 let frame=bytes.get(offset..end).ok_or(Error::Length{row})?;
 if call==log.fail_at {Err(log.error)}else{Ok((frame,end))}
}
fn prefix_control<'a>(bytes:&'a[u8],log:&mut PrefixLog)->Result<Prefix<'a>,Error>
'''+cut+'''
#[kani::proof] #[kani::unwind(35)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn prefix_value() {
 let n:usize=kani::any();kani::assume(n<=57607);let bytes=alloc::vec![0u8;n];let fail_at:usize=kani::any();kani::assume(fail_at<=27);let error=any_error();
 let starts:[usize;27]='''+str(starts).replace(' ','')+''';let widths:[usize;27]='''+str(widths).replace(' ','')+''';
 let mut log=PrefixLog{calls:0,fail_at,error,rows:[255;27],offsets:[0;27],lengths:[0;27]};let out=prefix_control(&bytes,&mut log);
 let mut stop=0usize;if n>=32 {while stop<27 {if starts[stop]+widths[stop]>n||stop==fail_at {break;}stop+=1;}}
 let expected_calls=if n<32 {0}else if stop<27 {stop+1}else{27};assert_eq!(log.calls,expected_calls);
 let k:usize=kani::any();kani::assume(k<27);
 let correct=if n<32 {matches!(out,Err(Error::Length{row:0}))}
 else if stop<27 {let expected=if starts[stop]+widths[stop]>n {Error::Length{row:stop as u8}}else{error};matches!(out,Err(e) if e==expected)}
 else if n!=13831 {matches!(out,Err(Error::TrailingBytes))}
 else {match out {Ok(prefix)=>prefix.c1_root.as_ptr()==bytes.as_ptr()&&prefix.records[k].as_ptr()==unsafe{bytes.as_ptr().add(starts[k])}&&prefix.records[k].len()==widths[k],Err(_)=>false}};
 assert!(correct!=cfg!(NGX_invert));if k<log.calls {assert_eq!(log.rows[k],k as u8);assert_eq!(log.offsets[k],starts[k]);assert_eq!(log.lengths[k],widths[k]);}
}
'''
p.write_text(s);o=json.loads((E/'NGX_OVERLAY.json').read_text());(E/'NGX_SOURCE_PINS.json').write_text(json.dumps({p:hashlib.sha256((E/n).read_bytes()).hexdigest() for p,n in o.items()},indent=1))
(E/'NGX_PREFIX_CUT.json').write_text(json.dumps(dict(original_body=original,cut_body=cut,callee_substitutions=count,only_changes=['parse_record_at -> local-record prefix_at_cut, same original arguments','Self constructor spelled Prefix outside impl'],starts=starts,widths=widths,terminal=13831),indent=1))
