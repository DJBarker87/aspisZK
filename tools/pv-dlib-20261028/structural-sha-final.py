"""Script-checked native SHA wrapper binding under ruling k', without Kani."""
from pathlib import Path
import subprocess,json,hashlib,re
R=Path(__file__).resolve().parents[2];E=R/'evidence/pv-dlib-20261028'
def clean(s):return re.sub(r'/\*.*?\*/|//[^\n]*','',s,flags=re.S)
def tokens(s):return re.findall(r'::|=>|[A-Za-z_]\w*|\d+|[^\s]',clean(s))
def body(s,needle):
 s=clean(s);a=s.index('{',s.index(needle));d=0
 for i in range(a,len(s)):
  if s[i]=='{':d+=1
  elif s[i]=='}':
   d-=1
   if not d:return s[a:i+1]
 raise ValueError(needle)
expected_final='''{
 let bs=Self::BlockSize::U64;
 let bit_len=8*(buffer.get_pos() as u64+bs*self.block_len);
 buffer.len64_padding_be(bit_len,|b|compress256(&mut self.state,from_ref(b)));
 for(chunk,v)in out.chunks_exact_mut(4).zip(self.state.iter()) {
 chunk.copy_from_slice(&v.to_be_bytes()); }
}'''
expected_pad='''{
 if suffix.len()>BlockSize::USIZE {panic!("suffix is too long");}
 let pos=self.get_pos();self.buffer[pos]=delim;
 for b in &mut self.buffer[pos+1..] {*b=0;}
 let n=self.size()-suffix.len();
 if self.size()-pos-1<suffix.len() {
 compress(&self.buffer);let mut block=Block::<BlockSize>::default();
 block[n..].copy_from_slice(suffix);compress(&block);
 } else {self.buffer[n..].copy_from_slice(suffix);compress(&self.buffer);}
 self.set_pos_unchecked(0)
}'''
code='''from pathlib import Path
import json,hashlib
r=Path('/home/dombarker/.cargo/registry/src/index.crates.io-1949cf8c6b5b557f');b=Path('/home/dombarker/project-offloads/codex-pv-dlib-20261028/native');out={}
for name in ['sha2-0.10.9/src/core_api.rs','block-buffer-0.10.4/src/lib.rs','block-buffer-0.10.4/src/sealed.rs']:
 p=r/name;s=p.read_bytes();actual=(b/name).read_bytes();assert actual.startswith(s),name
 out[name]=dict(path=str(p),sha256=hashlib.sha256(s).hexdigest(),source=s.decode(),private_copy_sha256=hashlib.sha256(actual).hexdigest(),prefix_matches=True)
print(json.dumps(out))
'''
r=subprocess.run(['ssh','dombarker@100.108.41.90','python3','-'],input=code,text=True,capture_output=True);assert r.returncode==0,r.stderr
files=json.loads(r.stdout);pins=json.loads((E/'native-prefix-pins.json').read_text())
for n,j in files.items():
 pin=next(x for x in pins if x['crate']+'/'+x['relative_path']==n);assert j['sha256']==pin['sha256'],n
final=body(files['sha2-0.10.9/src/core_api.rs']['source'],'fn finalize_variable_core')
pad=body(files['block-buffer-0.10.4/src/lib.rs']['source'],'pub fn digest_pad')
assert tokens(final)==tokens(expected_final),'native finalizer changed'
assert tokens(pad)==tokens(expected_pad),'native pad changed'
hp=R/'tools/pv-dlib-20261028/sha-final-helpers.rs';helper=hp.read_text();param=body(helper,'pub fn pv_dl_finalize_param')
normalized=param.replace('<Self as BlockSizeUser>::BlockSize','Self::BlockSize')
normalized=re.sub(r'\bcompress\b','compress256',normalized)
assert tokens(normalized)==tokens(final),'parameterization changed native control'
assert tokens(body(helper,'pub fn pv_dl_compress_slice'))==tokens('{compress256(state,blocks);}')
owned=R/'tools/pv-dlib-20261028/sha-final-native.rs'
j=dict(evidence_class='structural (K-1 substitute)',rulings=['r',"k'"],
 native_finalizer=dict(path=files['sha2-0.10.9/src/core_api.rs']['path'],body=final,tokens_match=True),
 native_padding=dict(path=files['block-buffer-0.10.4/src/lib.rs']['path'],body=pad,tokens_match=True),
 sources={n:{k:v for k,v in x.items() if k!='source'} for n,x in files.items()},
 parameterization=dict(path=str(hp.relative_to(R)),sha256=hashlib.sha256(hp.read_bytes()).hexdigest(),same_body_tokens_after_two_explicit_renamings=True,renamings=['type qualification Self::BlockSize','compression callback identifier only']),
 owned_reference=dict(path=str(owned.relative_to(R)),sha256=hashlib.sha256(owned.read_bytes()).hexdigest(),entry='owned'),
 differences=[
 dict(native='release u64 arithmetic, big-endian bit-length suffix',owned='wrapping arithmetic, explicit eight byte lanes',proofs=['PV_DL_LengthEncoding.length_value','PV_DL_LengthEncoding.suffix_length','PV_CBL_ShaBitLength.value']),
 dict(native='digest_pad suffixlen8, delim0x80, two-block branch64-pos-1<8',owned='owned split8 padding, pos>=56',proofs=['PV_DL_ShaBranches.padding','PV_DL_ShaBranches.suffix_fits','PV_CBL_PadContentSource.source','PV_DL_LengthEncoding.source']),
 dict(native='borrowed buffer writes; second block local; reset cursor0',owned='explicit returned first-buffer storage and cursor0',proofs=['PV_DL_FinalizeParam.source','PV_DL_ShaRestoration.buffer_restored']),
 dict(native='out.chunks_exact_mut(4).zip(state.iter()); copy_from_slice(be4)',owned='ordered flatMap of complete be4 stores',proofs=['PV_DL_ShaSerialize.source','PV_DL_ShaSerialize.length','PV_DL_ShaBranches.word_chunks','PV_DL_ShaBranches.word_indices','PV_DL_ShaRestoration.output_restored']),
 dict(native='GenericArray and Sha core private fields',owned='recursively nested native carrier shapes',proofs=['PV_DL_StorageBuild.reconstruct','PV_DL_ShaRestoration.selected_native'])],
 compression='arbitrary Result-valued single-block state transition; native compress256 receives from_ref(block); no backend semantics or backend equality assumed',
 complete_result_theorem='R1Z.PV_DL_ShaFinal.source_reference',selected_theorem='R1Z.PV_DL_ShaRestoration.selected_native',
 native_domain='Eager invariant pos<64; buffer64/output32/state8 words; frozen release overflow profile',
 finite_validation='sha-final-native-finite-resume/receipt.json (finite validation only; required before row credit)',
 kani=False,v232_untouched=True)
(E/'V231/structural-binding.json').write_text(json.dumps(j,indent=2)+'\n');print('full native padding/finalizer bodies and identical parameterized body checked')
