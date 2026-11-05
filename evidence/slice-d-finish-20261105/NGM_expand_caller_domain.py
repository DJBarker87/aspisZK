from pathlib import Path
import json,hashlib,subprocess,difflib
E=Path(__file__).resolve().parent;C='crates/aspis-r1-cost-probe/src/';inputs=json.loads((E/'NGM_NATIVE_INPUTS.json').read_text());s=inputs[C+'NGM_verifier.rs']
old='fn anyk()->K{q(kani::any())}'
new='fn anyk()->K{let words:[u32;4]=kani::any();for x in words{kani::assume(x<0x7fffffff);}q(words)}'
assert s.count(old)==1;s=s.replace(old,new)
helper='''fn canonical_message(bytes:&[u8],fields:usize){for i in 0..fields{for j in 0..8{let at=32*i+4*j;let word=u32::from_le_bytes([bytes[at],bytes[at+1],bytes[at+2],bytes[at+3]]);kani::assume(word<0x7fffffff);}}}
'''
s=s.replace('fn exercise(group:u8){',helper+'fn exercise(group:u8){')
s=s.replace('let bytes:[u8;2496]=kani::any();','let bytes:[u8;2528]=kani::any();canonical_message(&bytes[..224],7);canonical_message(&bytes[256..480],7);canonical_message(&bytes[480..],64);')
s=s.replace('variant:match kani::any::<u8>()%3{0=>Variant::S1,1=>Variant::S2,_=>Variant::D},roots:[[0;32];2],gamma:E::ZERO','variant:Variant::S2,roots:kani::any(),gamma:anye()')
s=s.replace('rho:K::ZERO,queries:[0;22]','rho:anyk(),queries:kani::any()').replace('claim:anye(),state:[0;32]','claim:anye(),state:kani::any()')
s=s.replace('inactive:E::ZERO,round0:&bytes[..224]','inactive:anye(),round0:&bytes[..224]').replace('round1:&bytes[224..448],final_message:&bytes[448..]','round1:&bytes[256..480],final_message:&bytes[480..]')
s=s.replace('let a=Accumulator{weights:alloc::vec![K::ZERO;64],rhs:anye(),power:K::ZERO,next:kani::any()};','let weight_values:[K;64]=core::array::from_fn(|_|anyk());let a=Accumulator{weights:weight_values.to_vec(),rhs:anye(),power:anyk(),next:kani::any()};')
assert 'weights:alloc::vec![K::ZERO;64]'not in s and 'bytes[224..448]'not in s
inputs[C+'NGM_verifier.rs']=s;(E/'NGM_NATIVE_INPUTS.json').write_text(json.dumps(inputs,indent=1)+'\n');pins=json.loads((E/'NGM_SOURCE_PINS.json').read_text());pins[C+'NGM_verifier.rs']=hashlib.sha256(s.encode()).hexdigest();(E/'NGM_SOURCE_PINS.json').write_text(json.dumps(pins,indent=1)+'\n')
patch=[]
for n,t in inputs.items():
 r=subprocess.run(['git','show','4bb3b3f:'+n],capture_output=True,text=True);patch+=difflib.unified_diff(r.stdout.splitlines(True),t.splitlines(True),fromfile='a/'+n if r.returncode==0 else'/dev/null',tofile='b/'+n)
(E/'NGM_harness.patch').write_text(''.join(patch))
(E/'NGM_CALLER_DOMAIN_REPAIR.json').write_text(json.dumps(dict(status='PENDING native checks K083..100',finding='D-CONTROL: prior finish-control scaffolds used zero accumulator weights and adjacent tail windows. Those observations cannot by themselves establish the general post-query caller domain.',replacement='same harness names, actual body, assertions and corruption controls; arbitrary canonical64 weights; all Prepared fields varied; full canonical message windows; actual TX2 relative offsets0..224,256..480,480..2528; inactive/power varied; S2 only',incoming='NGM_FinishDomain.AccumulatorDomain plus NFW Prepared/view boundary in NGM_DOMAIN.md',old_credit='K005..040 remain diagnostic/control fragments, never a CLOSED finish_relation row',budget_decision='Priority to the acceptance tail and domain fidelity: final18 native slots go to the expanded caller, not the unlaunched polynomial/round candidates',no_timeout_increase=True),indent=2)+'\n')
