"""Resolve the 62 empty roles from pinned definitions and their actual caller spans.
Classes describe source operation roles, never a transitive purity theorem.
"""
from pathlib import Path
import json,hashlib,collections
E=Path('evidence/pv-cx2-20261029');old=json.loads(Path('evidence/pv-cx-20261029/effect-interface.json').read_text());defs={r['id']:r for r in json.loads((E/'source-definitions-62.json').read_text())};sites={r['id']:r for r in json.loads((E/'unresolved-source-sites.json').read_text())}
groups=[
([27,28,29,30,31],['pure-library'],'Transaction configuration construction and field setters at main:18; the heap-size setter sets requested transaction metadata, not a host allocator request.'),
([33,93,132,417],['pure-library'],'Public-key projection, bytes/borrow, or derived zero Default at the inventoried call site; no key creation, signing, deletion, or entropy request.'),
([39],['pure-library','alloc','exit/panic'],'Compile the supplied instruction/account vectors into a message at main:19; memory collection and library error paths. This is local message construction, not an RPC send.'),
([56],['pure-library','alloc','exit/panic'],'anyhow macro error construction at inventoried macro-expanded call sites: Error::msg plus optional fmt::format; error/backtrace/environment runtime closure remains explicit, not stderr output at this call.'),
([82,215],['pure-library'],'Parse base58 address bytes from the supplied input string at the listed client sites, returning parse errors; not JSON parsing and not a random key generator.'),
([85,88,89,90,91,103,117,133,323,402],['pure-library','alloc','exit/panic'],'Derive PDA addresses/bump hints from supplied seeds at the listed plan sites. Native host hashing/curve search and its library allocation/runtime closure are retained; find_program_address has an explicit panic if no bump exists. No RPC or filesystem call at this operation.'),
([92,112,337,398],['pure-library'],'In-memory equality, identity error wrapper, Duration-to-f64 conversion, or string length at the listed site. Duration conversion at plan:129 does not read a clock; the earlier Instant::elapsed operation does.'),
([98,106,121,128,153,246,258,309],['pure-library','exit/panic'],'Validate/decode caller-supplied account bytes, choose a lane, construct/validate a leaf, or project semantic public data. Files/RPC acquisition happens in other source operations; indexing/unwrap/callee failure obligations are retained.'),
([135,157,159,165,169,179,303,316,324],['pure-library','exit/panic'],'Encode caller-supplied structures into fixed-size byte arrays (or return format errors); actual file/JSON/output effects are later distinct call sites. Slice/copy/runtime failure adequacy remains open.'),
([145,152,234,262,499],['pure-library','alloc','exit/panic'],'Deterministic digest/key/commitment or Merkle-parent computation from supplied data, via the named hash helper. No entropy source at these call sites; allocation/runtime/hash-refinement obligations are retained.'),
([147,327],['pure-library','alloc','exit/panic'],'Encode instruction bytes into a Vec using to_vec or with_capacity/extend_from_slice. This requests heap storage, not a filesystem write or network send.'),
([276,277],['pure-library','alloc','exit/panic'],'Compile the supplied forest witness, public values, context and snapshot into relation/trace data at plan:105; compile_forest_from_copies is a computation with memory allocation. No compiler process, file write, RPC or fresh entropy is invoked at this source operation.'),
([328],['pure-library','alloc','exit/panic'],'Validate nullifier encoding, hash the marker seed and call create_with_seed at plan:124. This computes an address; it does not create an on-chain account or perform a transaction.'),
([342,517],['pure-library','exit/panic'],'Integer division/ceiling or radix parsing; source-call operands retained (plan:129 and unhex:24). Division by zero and invalid radix remain failure obligations at the general library signature.'),
([228,229,240,373,458,526],['pure-library'],'Opaque constant initializer: no static Call/Drop sites. Retained as a constant dependency, not invented as a dynamic effect. Public scalar/digest tables are read by the client.')]
assign={}
for ids,cls,note in groups:
 for i in ids:assert i not in assign;assign[i]=(cls,note)
assert set(assign)==set(defs)
for r in old['opaque_functions']:
 i=r['llbc_fun_id']
 r['rust_ident_path']='::'.join(t['Ident'][0] for t in r['rust_name_structured'] if 'Ident' in t)
 r['classification_status']='inherited unverified candidate; not a new source audit'
 if i not in defs:continue
 r['classification_status']='resolved source operation role; transitive effect laws remain open'
 assert r['effect_class']==[]
 cls,note=assign[i];r['effect_class']=cls;r['classification_note']=note
 r['classification_evidence']=dict(definition_source=defs[i],source_call_excerpts=sites[i]['call_sites'],method='Manual source-role classification from exact definition and caller spans; not a source-model law or proof of transitive effect freedom')
 if i==56:r['additional_effects_retained']=['Error::msg backtrace capture and possible environment-read closure; not classified as pure execution']
old['status']='Charon source-role inventory: all 62 formerly empty classifications resolved; Aeneas/Lean status recorded separately'
old['limitations']=[v for v in old['limitations'] if 'Empty effect_class' not in v]+['Nonempty classes identify operation roles and conservative hazards, not discharged effect laws. All previous nonempty labels are inherited candidates pending separate audit; serialized generic-type substring matches may be misleading.']
(E/'effect-interface.json').write_text(json.dumps(old,indent=2)+'\n')
checks=dict(previously_empty=62,resolved=len(assign),remaining_empty=sum(not r['effect_class'] for r in old['opaque_functions']),all_call_sites_retained=True,source_definitions_sha256=hashlib.sha256((E/'source-definitions-62.json').read_bytes()).hexdigest(),rows_removed=[])
assert checks['remaining_empty']==0
(E/'effect-classification-checks.json').write_text(json.dumps(checks,indent=2)+'\n');print(json.dumps(checks))
