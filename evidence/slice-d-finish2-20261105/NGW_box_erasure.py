from pathlib import Path
import json,hashlib,subprocess,re
E=Path(__file__).resolve().parent;C='crates/aspis-r1-cost-probe/src/'
frozen=subprocess.check_output(['git','show','4bb3b3f:'+C+'weights.rs'],text=True)
assert 'fn box_from_parts(variant:Variant,factors:[[[K;4];5];5],points:[[K;10];3],extra:[K;2])->Box<Self> {\n        Box::new(Self { variant, factors, points, extra })\n    }' in frozen
s=json.loads((E/'NGW_NATIVE_INPUTS.json').read_text())[C+'NGW_new.rs']
expected='fn allocation(w:Weights,log:&mut BoxLog)->Box<Weights>{let out=Box::new(w);log.allocated=&*out;log.calls+=1;out}'
assert expected in s
assert 'fn source_box(variant:Variant,factors:Factors,points:[[K;10];3],extra:[K;2],log:&mut BoxLog)->Box<Weights>{allocation(Weights{variant,factors,points,extra},log)}'in s
assert all(word not in s for word in ['static mut','Option<fn','AtomicUsize'])
(E/'NGW_BOX_ERASURE.json').write_text(json.dumps(dict(frozen_revision='4bb3b3f51e16b4525f1d10336e2b0bcbbd775387',frozen_file_sha256=hashlib.sha256(frozen.encode()).hexdigest(),allocation_hook_sha256=hashlib.sha256(expected.encode()).hexdigest(),actual_value_packets='K079/080 variant; K081/K090 factor; K083/084 points; K085/086 extra (actual frozen box_from_parts)',ownership_packet='K087/088; same call Box::new then local pointer/count record; erased hook exactly Box::new(Weights{variant,factors,points,extra})',ghost_frame='local BoxLog only; no writable static, callback or caller memory write',controls='actual boxed-value corruption; distinct still-live allocation returned in ownership control',errors='safe Box::new has no recoverable error; fresh unique allocation or abort is the existing named Allocator trust under (aa); no availability premise',allocator_trust='retained/reclassified, never removed',status='PASS source-erasure inspection; native and model replay still required for closure'),indent=2)+'\n')
print('Box allocation-hook erasure checked')
