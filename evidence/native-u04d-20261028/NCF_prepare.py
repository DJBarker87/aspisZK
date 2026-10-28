from pathlib import Path
import json,hashlib
E=Path(__file__).resolve().parent;P=E.parent/'native-u04c-20261028'
s='\n'.join((P/'NCC_fullframes.rs.txt').read_text().splitlines()[:7]).replace('NCC_','NCF_')+'\n'
for slot,ty in [(29,'VerifierRegistryEntryV2'),(30,'VerifierRegistryEntryV1')]:
 s+=f'''#[kani::proof_for_contract({ty}::is_active_at)]
#[kani::unwind(33)]
fn NCF_op{slot}_contract(){{let r=NCF_any_{ty}();let slot:u64=kani::any();r.is_active_at(slot);}}
#[kani::requires(true)]
#[kani::ensures(|result: &bool| *result != (r.status == VerifierEntryStatusV1::Active && r.activation_slot <= slot && (r.retirement_slot == u64::MAX || slot < r.retirement_slot)))]
fn NCF_op{slot}_inverse(r:&{ty},slot:u64)->bool{{r.is_active_at(slot)}}
#[kani::proof_for_contract(NCF_op{slot}_inverse)]
#[kani::unwind(33)]
fn NCF_op{slot}_contract_negative(){{let r=NCF_any_{ty}();let slot:u64=kani::any();NCF_op{slot}_inverse(&r,slot);}}
#[kani::proof]
#[kani::stub_verified({ty}::is_active_at)]
#[kani::unwind(33)]
fn NCF_op{slot}_contract_use(){{let r=NCF_any_{ty}();let slot:u64=kani::any();let got=r.is_active_at(slot);assert_eq!(got,r.status == VerifierEntryStatusV1::Active && r.activation_slot <= slot && (r.retirement_slot == u64::MAX || slot < r.retirement_slot));}}
#[kani::proof]
#[kani::stub_verified({ty}::is_active_at)]
#[kani::unwind(33)]
fn NCF_op{slot}_contract_use_negative(){{let r=NCF_any_{ty}();let slot:u64=kani::any();let got=r.is_active_at(slot);assert_ne!(got,r.status == VerifierEntryStatusV1::Active && r.activation_slot <= slot && (r.retirement_slot == u64::MAX || slot < r.retirement_slot));}}
'''
(E/'NCF_slots.rs.txt').write_text(s)
(E/'NCF_gate.py').write_text((P/'NCC_gate.py').read_text().replace('NCC_frozen_graph','NCF_frozen_graph'))
(E/'NCF_batch_host.py').write_text((P/'NCC_batch_host.py').read_text())
(E/'NCF_frozen_graph.sha256').write_text((P/'NCC_frozen_graph.sha256').read_text())
