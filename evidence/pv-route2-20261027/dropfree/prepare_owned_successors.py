from pathlib import Path
D=Path(__file__).resolve().parent
for op in [205,212,215,216,219]:(D/'probes'/f'{op}-loop-rejected.rs').write_bytes((D/'probes'/f'{op}.rs').read_bytes())
s=(D/'probes/205.rs').read_text();a=s.index('fn compress(');b=s.index('pub fn new()',a)
c=s[a:b].replace('fn compress(state:&mut [u32;8],block:&[u8;64]){','#[inline(never)] fn compress(mut state:[u32;8],block:[u8;64])->[u32;8]{');at=c.rfind('}');c=c[:at]+'state\n'+c[at:]
header=s[:a]+c+s[b:s.index('pub fn update(')]
pack='#[inline(never)] fn pack(state:[u32;8])->[u8;32]{['+','.join(f'(state[{i}]>>{8*(3-j)}u32) as u8' for i in range(8) for j in range(4))+']}\n'
rest='''#[inline(never)] fn copy_bytes(mut buffer:[u8;64],offset:usize,input:&[u8],start:usize,count:usize)->[u8;64]{
 let mut i=0usize;while i<count {buffer[offset+i]=input[start+i];i+=1;}buffer
}
#[inline(never)] fn pad(mut buffer:[u8;64],pos:usize)->[u8;64]{buffer[pos]=128;let mut i=pos+1;while i<64 {buffer[i]=0;i+=1;}buffer}
#[inline(never)] fn length(mut buffer:[u8;64],bits:u64)->[u8;64]{
'''+''.join(f'buffer[{56+i}]=(bits>>{8*(7-i)}u32) as u8;\n' for i in range(8))+'''buffer}
pub fn update(s:&mut Sha256,input:&[u8]){
 let start=s.pos;let rem=64-start;let n=input.len();let mut i=0usize;
 if n<rem {s.buffer=copy_bytes(s.buffer,start,input,0,n);s.pos=start+n;return;}
 if start!=0 {s.buffer=copy_bytes(s.buffer,start,input,0,rem);s.state=compress(s.state,s.buffer);s.blocks=s.blocks.wrapping_add(1);i=rem;}
 while n-i>=64 {let block=copy_bytes([0u8;64],0,input,i,64);s.state=compress(s.state,block);s.blocks=s.blocks.wrapping_add(1);i+=64;}
 let tail=n-i;s.buffer=copy_bytes(s.buffer,0,input,i,tail);s.pos=tail;
}
pub fn finalize_variable_core(s:&mut Sha256)->[u8;32]{
 let bit_len=(s.pos as u64).wrapping_add(64u64.wrapping_mul(s.blocks)).wrapping_mul(8);let pos=s.pos;
 s.buffer=pad(s.buffer,pos);
 if pos>55 {s.state=compress(s.state,s.buffer);let block=length([0u8;64],bit_len);s.state=compress(s.state,block);}
 else {s.buffer=length(s.buffer,bit_len);s.state=compress(s.state,s.buffer);}
 s.pos=0;pack(s.state)
}
pub fn finalize_fixed_core(s:&mut Sha256,out:&mut [u8;32]){*out=finalize_variable_core(s);}
pub fn finalize_into(mut s:Sha256,out:&mut [u8;32]){finalize_fixed_core(&mut s,out);}
pub fn finalize(s:Sha256)->[u8;32]{let mut out=[0u8;32];finalize_into(s,&mut out);out}
'''
for op in [205,212,215,216,219]:(D/'probes'/f'{op}.rs').write_text(header+pack+rest)
p=D/'probes/36.rs';(D/'probes/36-loop-rejected.rs').write_bytes(p.read_bytes());s=p.read_text();a=s.index('pub fn array_try_from');s=s[:a]+'#[inline(never)] fn at<T:Copy,const CAP:usize>(v:Buffer<T,CAP>,i:usize)->T {v.data[i]}\n'+s[a:];s=s.replace('out[i]=v.data[i]','out[i]=at(v,i)');p.write_text(s)
