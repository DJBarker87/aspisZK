"""Named semantic review, domains and source-cut checks for added D packets.
No horizontal row or caller closes by citation alone.
"""
from pathlib import Path
import subprocess,re,hashlib,json
E=Path(__file__).resolve().parent;R=E.parents[1]
F='crates/aspis-core/src/field.rs::';W='crates/aspis-core/src/field/wide_exact.rs::';H='crates/aspis-core/src/state_only_hiding.rs::';Z='programs/r1-cost-probe/src/r1_pool_adapter_owned.rs::'
DETAILS={
 F+'CM31::square':dict(p=20,n=21,root='NFT_Square.source',copy=(22,23),domain='Canonical same CM31 receiver a,b<P',extra=[],roots=['NFT_Square.wide_product','NFT_Square.generated_scalar_product'],exclude=[F+'CM31::double',F+'CM31::mul'],proof='The static scalar receivers resolve to M31, not CM31. The two exact logged operand sites are discharged by wide_product and generated_scalar_product; all replies lie in the native oracle domains. reduce_u64 accepts every u64, and M31::double receives the canonical product. source gives the complete canonical two-word result.',files=['NFT_SQUARE_ERASURE.json','NFT_square.rs.txt']),
 W+'WideExact::neg':dict(p=14,n=15,root='NFT_WideNeg.source',copy=(10,11),domain='All eight limbs of the same WideExact receiver are canonical',extra=[],roots=['NFT_NegWord.source','NFT_NegSub.scalar'],exclude=[W+'WideExact::neg'],proof='The inventory self-edge is a union-resolution alternative: frozen self.c0/self.c1 are QM31, so their actual neg receivers are canonical QM31. E003 safe eight-word reference, wrapping neg word and zero-minus emitted theorems establish exact complete output. Existing CLOSED QM31 neg and subtraction packets are retained; no recursive WideExact call is executed.',files=['NFT_WideNeg.lean','NFT_WideReference/Funs.lean']),
 F+'qm31_from_karatsuba_channel_sums':dict(p=36,n=37,root='NFT_Karatsuba.source',copy=(32,33),domain='All nine raw u64 channel sums, without a product-budget assumption',extra=[],roots=['NFT_Karatsuba.total','NFT_Karatsuba.mul_r_value'],exclude=[F+'QM31::add',F+'QM31::sub',W+'WideExact::add',W+'WideExact::sub'],proof='Frozen static receiver reconstruction is CM31; reduce_u64 accepts all u64, every reduction/subtraction is canonical, and each exact CM31 add/sub receives canonical operands. The reached m1 is canonical (native assertion plus total reduction theorem); mul_r_value supplies the sole opaque reply on that same m1. Exact G substitution and total prove full result with no execution premise.',files=['NFT_KARATSUBA_ERASURE.json','NFT_karatsuba.rs.txt']),
 H+'cm31_mul_r':dict(p=59,n=60,root='NFT_Cmr.source',copy=(61,62),domain='Canonical same CM31 receiver a,b<P',extra=[],roots=['NFT_Cmr.double_value','NFT_Cmr.sub_value','NFT_Cmr.add_value'],exclude=[F+'CM31::add',F+'CM31::double',F+'CM31::sub',F+'QM31::add',F+'QM31::sub',W+'WideExact::add',W+'WideExact::sub'],proof='Exact four-site ANF logs double(a),sub(reply,b),double(b),add(a,reply) with canonical original and prior replies. Receivers resolve to M31; only final CM31::new uses the record constructor (all raw inputs allowed). Each same scalar child is paired with its total canonical value law; NFQ_Linear.source gives the complete natural value. No direct native multiplication claim.',files=['NFT_CMR_ERASURE.json','NFT_cmr.rs.txt']),
 Z+'require_zero':dict(p=48,n=49,root='NFT_ZeroJoin.source_and_frame',copy=(58,57),domain='Valid same immutable checkpoint slice length≤4096; deployed S2 caller fixes length1768',extra=[(50,51),(52,53),(54,55)],roots=['NFT_ZeroPhysical.physical_view','NFT_ZeroPhysical.pointer_step','NFT_ZeroJoin.checkpoint_bound'],exclude=[],proof='One native arbitrary suffix of completely arbitrary backing4096 has controlled exact pointer shift, Result/tag, length and immutable frame. pad/window/suffix laws preserve the same input, allocation and offset. source_and_frame joins these to NFQ finite-loop source equivalence and induction, without pointer or successful-result hypotheses. Frozen sole deployed owned caller checks S2 checkpoint_size=1768 before SDK borrow and passes that same borrow to require_zero; approved SDK same-account view law retained.',files=['NFT_ZERO_ERASURE.json','NFT_zero.rs.txt']),
 F+'qm31_pack_base4':dict(p=40,n=41,root='NFT_PackWords.source',copy=(38,39),domain='Same canonical visible input slice, length0..4, with explicit zero initializer padding',extra=[(42,43),(44,45),(46,47)],roots=['NFT_Pack.graph','NFT_Pack.padded_canonical','NFT_PackPrefix.source'],exclude=[],proof='All four native coordinate checks quantify every length0..4 and visible input, execute real constant-coefficient arithmetic and reductions. Generic copyPrefix theorem proves untouched zero tail and exact visible prefix. graph joins the original wrapper and actual four-term emitted tail on that same padded input; PackWords.source gives all four exact raw coordinates. reduce_u64 has all-u64 domain and CM31::new has all-raw domain. No variable field product in Kani.',files=['NFT_pack.rs.txt','NFT_Pack.lean']),
 F+'qm31_m31_dot':dict(p=76,n=77,root='NFT_DotSource.source',copy=(74,75),domain='Same two canonical slices of equal length7; sole Slice D parent interpolated_internal_pair constructs exactly7 rows',extra=[(63,64),(65,66),(70,73)],copy_extra=[(71,72)],roots=['NFT_Dot.scalar_product','NFT_Dot.control','AspisR1.FJh_M31DotInput.source_success','AspisR1.FJh_M31DotChunkModel.loop_success_fuel'],exclude=[],proof='K076/077 select the same weight/value read at arbitrary index<7, four ordered product operands/replies and full raw poststate. K063/064 cover arbitrary-prestate term; K065/066 real reducer fold; K070/073 cover data-independent two chunks and eight folds. Product/value and accumulator bounds are established by scalar_product and the existing exact term/loop induction; source is full coherent FIq seven-term emitted function, canonical reconstruction and decoded sum. The only D parent constructs ROWS=[2,3,4,5,6,7,8], so length7 is caller-established; other lengths are unclaimed. Static CM31 new accepts all raw values; reducer all u64.',files=['NFT_dot.rs.txt','NFT_DotSource.lean']),
 F+'qm31_sum_products3_prepared':dict(p=92,n=93,root='NFT_PreparedSum3.source',copy=(94,95),domain='Same three left caches satisfying PreparedFor canonical original inputs, and same three canonical right inputs',extra=[(90,91),(96,97)],roots=['NFT_PreparedSum3.constructor_domain','NFT_PreparedFrame.frame','NFT_PreparedFrame.control','AspisR1PoseidonPreparedChannelRunStepLocal.runStep_success','AspisR1PoseidonPreparedChannelLoopExact.loop_success_fuel'],exclude=[F+'QM31::add',W+'WideExact::add'],proof='The fixed27-cut control, exact frozen right prefix, and arbitrary-prestate selected native cell/frame are independently controlled. PreparedFor includes canonical components; NFQ_PreparedDomain.output_domain proves every constructor cache word<P on the same input. Native prestate<3*2^62 includes actual ≤2*(P-1)^2, established by three-product loop invariant; emitted runStep_success supplies exact same product and nested array back closure, NFT_PreparedFrame.frame supplies all other cells, and loop_success_fuel supplies induction. Full source theorem retains PreparedFor for actual caches and exact decoded sum, not independent child-result assumptions. Cache M31/CM31 additions are canonical; final nine-u64 converter accepts all raw sums and is newly CLOSED here.',files=['NFT_PREPARED_ERASURE.json','NFT_prepared.rs.txt'])}

def body(s,marker):
 start=s.index(marker);a=s.index('{',start);depth=1;b=a+1
 while depth:depth+=(s[b]=='{')-(s[b]=='}');b+=1
 return s[a+1:b-1]
def compact(s):return re.sub(r'\s+','',re.sub(r'//[^\n]*','',s))
def checks():
 src=subprocess.check_output(['git','show','4bb3b3f51e16b4525f1d10336e2b0bcbbd775387:crates/aspis-core/src/field.rs'],cwd=R,text=True)
 # Checks added to the unchanged NFQ/NFK validator. Compare source strings, not receipt booleans.
 for script in ['NFT_square_erasure.py','NFT_cmr_erasure.py']:
  subprocess.run([__import__('sys').executable,str(E/script)],check=True,capture_output=True)
 j=json.loads((E/'NFT_KARATSUBA_ERASURE.json').read_text());assert j['frozen_body']==body(src,'fn qm31_from_karatsuba_channel_sums(')
 assert j['instrumented_body'].replace('mul_r(log,m1)','mul_by_r(m1)')==j['frozen_body']
 assert j['instrumented_body']in(E/'NFT_karatsuba.rs.txt').read_text()
 p=(E/'NFT_prepared.rs.txt').read_text();f=body(src,'pub fn qm31_sum_products3_prepared(');prefix=f[f.index('        let right_sum ='):f.index('        for component in 0..3 {')]
 assert prefix in p
 site='sums[component][channel] += left[index].components[component][channel].0 as u64 * right_components[component][channel].0 as u64;'
 assert compact(site)in compact(f)
 assert compact('sums[component][channel]+=product(log,index,component,channel,left[index].components[component][channel].0 as u64,right_components[component][channel].0 as u64);')in compact(p)
 assert 'for index in 0..3{for component in 0..3{for channel in 0..3{'in p
 dot=body(src,'pub fn qm31_m31_dot(');d=(E/'NFT_dot.rs.txt').read_text()
 for i,path in enumerate(['c0.a','c0.b','c1.a','c1.b']):
  assert compact(f'raw[{i}] += weight.{path}.0 as u64 * value;')in compact(dot)
  assert compact(f'raw[{i}]+=product(log,u64::from(weight.{path}.0),value);')in compact(d)
 assert 'let value = values[index].0 as u64;'in dot and 'let weight = weights[index];'in dot
 assert 'let value=values[index].0 as u64;let weight=weights[index];term_cut(raw,weight,value,log)'in d
 assert 'sums[index] += M31::reduce_u64(raw[index]).0 as u64;'in dot
 assert 'for start in (0..weights.len()).step_by(4)'in dot
 caller=subprocess.check_output(['git','show','4bb3b3f:crates/aspis-statement/src/state_only_poseidon.rs'],cwd=R,text=True)
 assert 'const ROWS: [usize; 7] = [2, 3, 4, 5, 6, 7, 8];'in caller
 owned=subprocess.check_output(['git','show','4bb3b3f:programs/r1-cost-probe/src/r1_pool_adapter_owned.rs'],cwd=R,text=True)
 assert 'checkpoint_size(Variant::S2)'in owned and owned.count('require_zero(checkpoint_data)')==1
 zero=body((E/'NFT_zero.rs.txt').read_text(),'fn zero_cut(')
 erased=zero.replace('if !remaining.is_empty()','while !remaining.is_empty()',1).replace('return (1,remaining,Err(ProgramError::AccountAlreadyInitialized));','return Err(ProgramError::AccountAlreadyInitialized);').replace('return (2,remaining,Ok(()));','').replace('(0,remaining,Ok(()))','Ok(())')
 assert compact(erased)==compact(body(owned,'fn require_zero('))
 for n in ['NFT_zero.rs.txt','NFT_dot.rs.txt','NFT_prepared.rs.txt','NFT_square.rs.txt','NFT_karatsuba.rs.txt','NFT_cmr.rs.txt']:
  s=(E/n).read_text();assert not re.search(r'\bstatic\s+(?:mut\s+)?\w',s)
 return True
