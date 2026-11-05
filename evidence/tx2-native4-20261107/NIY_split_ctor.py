from pathlib import Path
import json,hashlib,difflib
E=Path(__file__).resolve().parent;x=json.loads((E/'NIY_NATIVE_INPUTS.json').read_text());n='crates/aspis-r1-cost-probe/src/NIY_ctor_payload.rs';old=x[n];s=old
s=s.replace('let raw=kani::vec::any_vec::<[u32;4],64>();kani::assume(raw.len()==64);','let raw:[[u32;4];64]=kani::any();')
s=s.replace('raw.into_iter().map(|x|K{c0:CM31{a:M31(x[0]),b:M31(x[1])},c1:CM31{a:M31(x[2]),b:M31(x[3])}}).collect()','alloc::vec::Vec::from(raw.map(|x|K{c0:CM31{a:M31(x[0]),b:M31(x[1])},c1:CM31{a:M31(x[2]),b:M31(x[3])}}))')
a=s.index(' let roots=p.roots;');b=s.index(' let mut allocation=0;',a);s=s[:a]+s[b:]
a=s.index(' let b:usize=kani::any();');b=s.index('\n}',a)
s=s[:a]+''' // One selected payload window plus scalar descriptor/guard observations.
 assert_eq!(out.as_ref() as *const Prepared as usize,allocation);
 assert_eq!(after.next,next_byte as usize);assert_eq!(after.weights.as_ptr() as usize,pointer);assert_eq!(after.weights.len(),64);assert_eq!(after.weights.capacity(),capacity);assert_eq!(kw(after.weights[wi],j),selected);
'''+s[b:]
assert s!=old and 'fn ctor_payload(){check();}' in s
x[n]=s;(E/'NIY_NATIVE_INPUTS.json').write_text(json.dumps(x,indent=2)+'\n');(E/'NIY_ctor_payload.rs.txt').write_text(s)
pins=json.loads((E/'NIY_SOURCE_PINS.json').read_text());pins[n]=hashlib.sha256(s.encode()).hexdigest();(E/'NIY_SOURCE_PINS.json').write_text(json.dumps(pins,indent=2)+'\n')
(E/'NIY_CTOR_SPLIT.diff').write_text(''.join(difflib.unified_diff(old.splitlines(True),s.splitlines(True),fromfile='K035_full_constructor',tofile='split_selected_window')))
rows=json.loads((E/'NIY_NATIVE_MATRIX.json').read_text());r=rows[18];r['excluded_full_attempt']='NIY_K035';r['status']='planned split after timeout';r.pop('positive',None);r.pop('positive_qualified',None);r['domain']='S2 arbitrary prepared fields; all64 arbitrary Rust-valid K cells at length64/capacity64; one arbitrary cell/limb; full end guard, next cast and descriptor; capacity64 caller producer remains an independent obligation';r['shape']='one selected payload window; no complete Prepared-field native claim';(E/'NIY_NATIVE_MATRIX.json').write_text(json.dumps(rows,indent=2)+'\n')
(E/'NIY_CTOR_DOMAIN_FINDING.md').write_text('''# NIY constructor domain finding

K035 full arbitrary64-weight constructor timed out; no credit. The replacement checks one arbitrary selected payload cell and scalar descriptor/guard fields, retaining all64 arbitrary values in the valid input. Harness names, caps and90s timeout are unchanged. Input setup is a fixed64-word array mapped into Vec; it is not a verifier algorithm loop certificate.

Both constructions materialize capacity64. Do not claim arbitrary capacity or instantiate the actual caller before deriving that capacity from its SAME reserve/resize/read-weights producer. NIG filled045 checks pointer/capacity stability for native resize steps; the initial actual reserve capacity and its source-occurrence binding need an independent law. This is an OPEN native caller-domain finding, not a whole resume pass. Prepared native-field facets retain NIL's original stated domain; the new Lean final port maps all exact fields but is not native ownership evidence.
''')
print('Split K035 into one arbitrary payload window with all64 values arbitrary; preserved harness names, exposed capacity64 caller obligation.')
