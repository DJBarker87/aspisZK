from pathlib import Path
import json,hashlib
E=Path(__file__).resolve().parent;x=json.loads((E/'NGH_NATIVE_INPUTS.json').read_text());n='crates/aspis-core/src/field.rs';s=x[n]
s=s.replace('(r[NGH_reference::OBS/3][NGH_reference::OBS%3]==NGH_reference::NGH_accumulate_ref(sums,left,right)[NGH_reference::OBS/3][NGH_reference::OBS%3])','(((r[NGH_reference::OBS/3][NGH_reference::OBS%3]>>NGH_reference::SHIFT)&NGH_reference::MASK)==((NGH_reference::NGH_accumulate_ref(sums,left,right)[NGH_reference::OBS/3][NGH_reference::OBS%3]>>NGH_reference::SHIFT)&NGH_reference::MASK))')
x[n]=s
n='crates/aspis-core/src/NGH_reference.rs';s=x[n]
s=s.replace('if cell==OBS{now==old+if done{native_product(a.0 as u64,b.0 as u64)}else{0}}','if cell==OBS{if done{now<=old+4611686009837453316&&((now>>SHIFT)&MASK)==(((old+native_product(a.0 as u64,b.0 as u64))>>SHIFT)&MASK)}else{now==old}}')
s+='\npub(super) const SHIFT:u32=if cfg!(NGH_shift32){32}else{0};\npub(super) const MASK:u64=if cfg!(NGH_bits1){1}else if cfg!(NGH_bits8){255}else if cfg!(NGH_bits16){65535}else{4294967295};\n'
x[n]=s
(E/'NGH_NATIVE_INPUTS.json').write_text(json.dumps(x,indent=1)+'\n');(E/'NGH_SOURCE_PINS.json').write_text(json.dumps({n:hashlib.sha256(t.encode()).hexdigest()for n,t in x.items()},indent=1)+'\n');(E/'NGH_reference_bits.rs.txt').write_text(s)
p=E/'NGH_run.py';s=p.read_text().replace("if os.environ.get('NGH_OBSERVE'):env['RUSTFLAGS']+=' --cfg NGH_observe_'+os.environ['NGH_OBSERVE']", "if os.environ.get('NGH_OBSERVE'):env['RUSTFLAGS']+=' --cfg NGH_observe_'+os.environ['NGH_OBSERVE']\n if os.environ.get('NGH_BITS'):env['RUSTFLAGS']+=' --cfg NGH_bits'+os.environ['NGH_BITS']\n if os.environ.get('NGH_SHIFT32'):env['RUSTFLAGS']+=' --cfg NGH_shift32'")
p.write_text(s)
