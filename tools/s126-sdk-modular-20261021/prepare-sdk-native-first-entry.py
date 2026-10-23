#!/usr/bin/env python3
"""Original SDK entry precondition, stopping after assertions at tx1 entry.
Only first-entry byte/scalar/argument facts are claimed. The cut has no returned
first result, no post-call frame and no cleanup/termination claim. A pure
arbitrary688-byte comparison result overapproximates the real read-only call;
candidate value semantics are supplied separately by the checked source gate.
"""
from pathlib import Path
import subprocess,sys,json,hashlib
R=Path(__file__).resolve().parents[2];out=Path(sys.argv[1]);root=int(sys.argv[2]);args=sys.argv[3:]
subprocess.run(['python3',str(R/'tools/s126-sdk-modular-20261021/prepare-sdk-native-first-point.py'),str(out),str(root),*args],check=True)
p=out/'src/lib.rs';s=p.read_text();s=s.replace('\n frame_probe();','')
needle=' assert_eq!(unsafe{candidate.add(index).read()},plan().candidate[index],"both comparison candidates are the common typed encoder result at every coordinate");'
assert s.count(needle)==1;s=s.replace(needle,' // No candidate-coordinate claim in this unilateral read-only comparison overapproximation.')
needle='struct GhostStorage<T>{value:T,allocation_tag:u64}'
assert s.count(needle)==1
s=s.replace(needle,needle+'''
#[derive(Clone,Copy)] struct EntryScalars{counts:[isize;3],slots:[usize;3],account_count:usize,instruction_len:usize,instruction:[u8;3]}
static mut ENTRY_SCALARS:GhostStorage<Option<EntryScalars>>=GhostStorage{value:None,allocation_tag:0x51a8000000000001};
''')
needle=' Ok(Vec::new())';assert s.count(needle)==1
s=s.replace(needle,'''
 frame_probe();
 let input=unsafe{ENTRY_SCALARS.value.unwrap()};
 assert_eq!(input.account_count,3);assert_eq!(input.instruction_len,2);assert_eq!(input.instruction[0],3);
 assert!(input.instruction[1]==10 || input.instruction[1]==11);
 assert_eq!(input.slots,[0,1,2],"actual first entry derives all original data allocations");
 assert_eq!(input.counts[2],0);
 assert!(input.counts[0]>=0 && input.counts[0]<isize::MAX);
 assert!(input.counts[1]>=0 && input.counts[1]<isize::MAX);
 assert_eq!(unsafe{(*COUNTERS.value[0]).get()},input.counts[0]+1);
 assert_eq!(unsafe{(*COUNTERS.value[1]).get()},input.counts[1]+1);
 assert_eq!(unsafe{(*COUNTERS.value[2]).get()},-1);
 kani::cover!(true,"original SDK reaches checked first entry");
 kani::cover!(unsafe{(*COUNTERS.value[0]).get()}==isize::MAX,"first entry with maximum live shared counter");
 kani::assume(false);
 Ok(Vec::new())''')
needle=' unsafe{NATIVE_ROOT_PTRS.value=pointers;';assert s.count(needle)==1
s=s.replace(needle,''' unsafe{ENTRY_SCALARS.value=Some(EntryScalars{counts:initial_counts,slots:data_slots,account_count,instruction_len,instruction});}
'''+needle)
needle=' let actual=native_prefix(&program,&accounts[..account_count],&instruction[..instruction_len]);';assert s.count(needle)==1
s=s.replace(needle,needle+'\n kani::assume(false); // Return without first entry is outside this entry-precondition target.')
s='\n'.join(line for line in s.splitlines() if not line.startswith(' kani::cover!(unsafe{CALLS.value[0]}'))+'\n'
assert s.count('kani::cover!(')==2
# Kani may coalesce a bare mutable Option::None initializer with a promoted
# None constant used by observer(). Give retained callback its own tagged object.
s=s.replace('pub static mut s126_keep_coupled_cmp:Option<extern "C" fn(*const u8,*const u8,usize)->i32>=None;', 'pub static mut s126_keep_coupled_cmp:GhostStorage<Option<extern "C" fn(*const u8,*const u8,usize)->i32>>=GhostStorage{value:None,allocation_tag:0x51a9000000000001};')
s=s.replace('s126_keep_coupled_cmp=Some(s126_coupled_cmp)', 's126_keep_coupled_cmp.value=Some(s126_coupled_cmp)')
assert 'pub static mut s126_keep_coupled_cmp:GhostStorage<' in s
p.write_text(s)
p=out/'Cargo.toml';p.write_text(p.read_text().replace('first-frame-root','first-entry-root').replace('-v1"','-v2"'))
p=out/'source-cut.json';m=json.loads(p.read_text());m.update(source_sha256=hashlib.sha256(s.encode()).hexdigest(),qualification=__doc__,events=['first/tx1 entry only'],instrumentation_correction='Tagged retained callback object prevents Kani promoted None constant from aliasing the mutable callback storage. Original observer source remains exactly None. v1 windows4/11 exposed this codegen mismatch; no credit for their failures. New source requires fresh proof and generated observer-body audit.',entry_stop='Assertions and both reached-entry covers execute before kani::assume(false) in the actual verifier child hook. Ordinary native returns are also stopped. No first reply or post-entry behavior is assumed or claimed.',comparison_cut='Read-only arbitrary0/nonzero choice for the sole688-byte guard comparison. Original proof pointer and source order retained; candidate-coordinate equality is not a premise/property of this target. Both real outcomes included. Other comparisons use original libc model.',remaining='All entry assertions/safety/unwinding and both covers must pass. Need complete index/root coverage and same-execution instantiation. Source-gate value law, actual source scanner/typed-child installation, actual first continuation/writeback/drop and general runtime/source/oracle joins remain explicit.')
p.write_text(json.dumps(m,indent=2)+'\n')
