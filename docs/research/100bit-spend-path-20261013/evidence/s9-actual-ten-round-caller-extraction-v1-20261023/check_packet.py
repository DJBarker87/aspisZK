from pathlib import Path
import hashlib,json,re
r=Path(__file__).resolve().parent;sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest();m=json.loads((r/'manifest.json').read_text())
assert m['schema']=='focused-extractor-proof-packet-v1' and not m['compiled_objects_included']
for f in m['files']:
 p=r/f['path'];assert p.stat().st_size==f['bytes'] and sha(p)==f['sha256'],f['path']
s=json.loads((r/'source-origin/source-pins.json').read_text());cur=(r/'source-origin/r1_semantic.current.rs').read_bytes();cut=(r/'source-origin/r1_semantic.with-unused-entry.rs').read_bytes();suffix=(r/'source-origin/unused-forwarding-entry.rs').read_bytes()
assert cut==cur+suffix and b'focused_semantic_round_entry' in suffix
assert sha(r/'source-origin/r1_semantic.current.rs')==s['current_semantic_sha256']=='c66eba53bc3cdf801466455089d7189c02a0bec858f407a5fc9db35d10b17013'
assert sha(r/'source-origin/r1_semantic.with-unused-entry.rs')==s['source_cut_file_sha256']=='cb6922614de8c9866b604aacf69f28d760da0143867906f6796b4b3c1d3abef0'
a=json.loads((r/'extraction/charon/receipt.json').read_text());b=json.loads((r/'extraction/aeneas/receipt.json').read_text());assert a['exit_status']==b['exit_status']==0 and a['wrapper_exit_status']==1;assert a['root_body_nonempty'] and a['semantic_rounds_root_count']==1 and a['llbc_has_errors'] is False;assert a['scope_memory_peak_bytes'] is None
assert a['process_swaps']==0 and b['scope_swap_current_bytes']==0
for ph in ['charon','aeneas']:
 q=json.loads((r/'extraction'/ph/'admission-summary.json').read_text());assert all(q['checks'].values());z=json.loads((r/'extraction'/ph/'reservation.json').read_text());assert z['limits']['memory.max']=='2147483648' and z['limits']['memory.swap.max']=='0'
t=json.loads((r/'extraction/target-metadata.json').read_text());assert t['caller']['is_opaque'] is False and t['caller']['source']['begin_line']==133 and t['caller']['source']['end_line']==179 and not t['unused_shim_emitted']
assert (r/'raw-generated/Types.lean').read_bytes()==(r/'source-origin/Types.prior-raw.lean').read_bytes()
old=(r/'source-origin/Funs.prior-raw.lean').read_text();new=(r/'raw-generated/Funs.lean').read_text();old=old[old.index('def r1_semantic.semantic_round\n'):old.index('/-- [aspis_r1_cost_probe::r1_semantic::focused_semantic_round_entry]')].strip();fresh=new[new.index('def r1_semantic.semantic_round\n'):new.index('/-- [aspis_r1_cost_probe::r1_semantic::semantic_rounds]')].strip();assert old==fresh
assert 'axiom aspis_core.field.QM31.ZERO : Result' in (r/'raw-generated/FunsExternal_Template.lean').read_text()
for p in r.rglob('*'):
 if p.is_file():assert p.suffix not in {'.olean','.ilean','.llbc','.so','.dylib','.pyc'}
print('PASS: actual private caller extracted; exact prior Types/single-round reuse; current prefix+unused shim; scoped tool evidence/recovery boundary; source-only packet')
