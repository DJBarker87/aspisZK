#!/usr/bin/env python3
"""Native/reference first-entry pairing on the NECESSARY reached-first image.
This is NOT a claim for arbitrary inputs: native constructor-ready facts plus
existing exact scanner/gate laws must prove normalization is identity on every
actual reached-first input. Flags, owner, slots, counts, zero checkpoint,
688-byte candidate prefix and tag are normalized explicitly. Full SDK types,
statement, arbitrary remaining proof/public bytes, Rc/lamport state remain.
No SDK stubs or simplified carrier. First reply empty isolates the prefix.
"""
from pathlib import Path
import subprocess,json,hashlib,sys
R=Path(__file__).resolve().parents[2];O=Path(sys.argv[1]);assert not O.exists()
subprocess.run(['python3',str(R/'tools/s126-sdk-modular-20261021/prepare-sdk-native-first-entry-pair.py'),str(O)],check=True)
p=O/'src/lib.rs';s=p.read_text()
a=s.index('unsafe fn frozen_release_dealloc(');b=s.index('#[kani::proof] #[kani::unwind(48)]',a);s=s[:a]+s[b:]
s=s.replace('let owners:[Pubkey;3]=core::array::from_fn(|_|Pubkey::new_from_array(kani::any()));','let mut owners:[Pubkey;3]=core::array::from_fn(|_|Pubkey::new_from_array(kani::any()));owners[2]=program;')
s=s.replace('let flags:[[bool;3];3]=kani::any();','let flags:[[bool;3];3]=[[false,false,false],[false,false,false],[false,true,false]];\n kani::assume(keys[0]!=keys[1]&&keys[0]!=keys[2]&&keys[1]!=keys[2]);')
s=s.replace('let instruction:[u8;3]=kani::any();let instruction_len:usize=kani::any();kani::assume(instruction_len<=3);','let split:u8=kani::any();kani::assume(split==10||split==11);let instruction:[u8;3]=[3,split,0];let instruction_len:usize=2;')
s=s.replace('let account_count:usize=kani::any();kani::assume(account_count<=3);','let account_count:usize=3;')
s=s.replace('kani::vec::exact_vec::<u8,1768>()','vec![0;1768]')
s=s.replace('let data_slots:[usize;3]=kani::any();','let data_slots:[usize;3]=[0,1,2];')
needle='let initial_counts:[isize;3]=kani::any();';assert s.count(needle)==1
s=s.replace(needle,'''let proof_count:isize=kani::any();let public_count:isize=kani::any();
 kani::assume(proof_count>=0&&proof_count<isize::MAX&&public_count>=0&&public_count<isize::MAX);
 let initial_counts:[isize;3]=[proof_count,public_count,0];''')
s=s.replace('different:kani::any()','different:false')
needle=' let actual={';assert s.count(needle)==1
s=s.replace(needle,''' unsafe{std::ptr::copy_nonoverlapping(plan().candidate.as_ptr(),buffers[0].as_mut_ptr(),688);}
 buffers[0][696]=2;
'''+needle)
assert '#[kani::stub(AccountInfo::' not in s and 'frozen_release_dealloc' not in s
p.write_text(s);p=O/'Cargo.toml';p.write_text(p.read_text().replace('first-entry-pair-v5','first-image-pair-v1'))
(O/'source-cut.json').write_text(json.dumps(dict(schema='focused-extractor-proof-packet-v1',source_sha256=hashlib.sha256(s.encode()).hexdigest(),qualification=__doc__,expected_time='Cached optimized compilation, then paired first-prefix on normalized necessary image; alias/flag branches removed before symbolic execution, not increased caps.',remaining='All assertions/covers must pass. Independently prove input normalization identity using concrete native reached-first metadata/slot/count/tag facts and existing source scanner/gate semantics. Then first-entry causality/source children, full continuation/SDK effect and runtime/oracle/TX2 transport remain. This candidate cannot establish arbitrary-adversary or whole S2 closure by itself.'),indent=2)+'\n')
