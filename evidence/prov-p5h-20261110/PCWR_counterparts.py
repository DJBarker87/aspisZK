import json
V='crates/aspis-r1-cost-probe/src/verifier.rs'; C='crates/aspis-r1-cost-probe/src/compact.rs'
PIN='4bb3b3f51e16b4525f1d10336e2b0bcbbd775387'
rows=json.load(open('PCWR_rows_served.json'))
search=dict(
 by_name="git grep -w for each of the 12 unique key stems (check_values_owned finish_owned residue_owned value_owned body_byte decode_e_spec decode_k_spec e_byte encode_k k_byte k_from_limbs word_spec) in 4bb3b3f crates+programs and in Pool b936275 programs/aspis-pool: 0 hits for every stem (the models are tools-crate names).",
 by_shape=["Mersenne fold ('0x7fff_ffff' with '>> 31') in 4bb3b3f crates+programs: field.rs reduce, fast_dots.rs (four_dots_one, unrelated 8-limb variant) and crates/aspis-r1-cost-probe/src/verifier.rs update_residue_row (match for residue_owned/scalar_owned)",
  "'[u64; 4]' row type: crates/aspis-r1-cost-probe/src/verifier.rs:204 BatchedWeights {raw: Vec<[u64;4]>} (match for finish_owned/value_owned/residue_owned)",
  "compact K value check ('QM31::from_le_bytes ... NonCanonical'): crates/aspis-r1-cost-probe/src/compact.rs:139 check_values (match for check_values_owned); tools/s8-kani-20261021/src/frozen.rs:8 is the tool's own copy of it",
  "checkpoint layout 'R1P2CKP2' in 4bb3b3f: verifier.rs checkpoint (writer) and resume (reader); programs/r1-cost-probe only has a test",
  "from_limbs/to_limbs/write_le_bytes/to_le_bytes in aspis-core: QM31::write_le_bytes field.rs:1028, WideExact::to_limbs wide_exact.rs:238, WideExact::to_le_bytes wide_exact.rs:273; no QM31::from_limbs in aspis-core (only an unrelated crates/aspis-r1-cost-probe/src/fast_pairing.rs:24 from_limbs on a different type)",
  "Pool b936275 programs/aspis-pool: no hit for any shape"],
 sources_read=["tools/s8-kani-20261021/src/owned.rs (research)","tools/s8-kani-20261021/src/frozen.rs","tools/oracle-port-ckpt-abi2/src/lib.rs"])
S8='S8OwnedP6.Funs'; OP='OraclePortCkptAbi2Extracted.Funs'
def f(file,line,name,kind,note): return dict(frozen_function=dict(file=file,line=line,name=name,revision=PIN),relation=kind,note=note)
keys={}
keys[S8+'|S8OwnedP6.check_values_owned']=f(C,139,'check_values','COUNTERPART_FOUND','frozen loops with chunks_exact(16) (core slice iterator, HM-B row) and checks QM31::from_le_bytes(c).ok_or(CodecError::NonCanonical); the model is an index loop over compact.len()/16 with the same check; same error')
keys[S8+'|S8OwnedP6.check_values_owned_loop']=dict(frozen_function=None,relation='GATE_SIDE_LOOP_OF_COUNTERPART',parent='check_values_owned',note='gate-side while loop; frozen check_values has a for over chunks_exact, no loop item of this shape')
keys[S8+'|S8OwnedP6.check_values_owned_loop.body']=dict(frozen_function=None,relation='GATE_SIDE_LOOP_OF_COUNTERPART',parent='check_values_owned',note='as above')
keys[S8+'|S8OwnedP6.finish_owned']=f(V,226,'BatchedWeights::finish','COUNTERPART_FOUND','frozen: &self method, in-place iter_mut().enumerate() over weights writing self.value(i); model: consumes raw Vec<[u64;4]> and weights Vec<K> by value, index loop, returns the Vec (signature differs by reference-ownership restructuring)')
keys[S8+'|S8OwnedP6.finish_owned_loop']=dict(frozen_function=None,relation='GATE_SIDE_LOOP_OF_COUNTERPART',parent='finish_owned',note='gate-side while loop; frozen uses iter_mut().enumerate()')
keys[S8+'|S8OwnedP6.finish_owned_loop.body']=dict(frozen_function=None,relation='GATE_SIDE_LOOP_OF_COUNTERPART',parent='finish_owned',note='as above')
keys[S8+'|S8OwnedP6.residue_owned']=f(V,235,'update_residue_row','COUNTERPART_FOUND','frozen mutates row in place (limb products via residue_limb_at/power_limb_at, then a flush loop over the row); model is the pure function returning [u64;4] with scalar_owned per limb (scalar_owned is not an OPEN key)')
keys[S8+'|S8OwnedP6.value_owned']=f(V,222,'BatchedWeights::value','COUNTERPART_FOUND','frozen: &self method reducing self.raw[index] with M31::reduce_u64 (array map); model: takes the row [u64;4] directly')
for k in ['body_byte','decode_e_spec','decode_k_spec','e_byte','encode_k','k_byte','k_from_limbs','word_spec']:
    keys[OP+'|OraclePortCkptAbi2Extracted.'+k]=dict(frozen_function=None,relation='NONE')
rel={
 'body_byte':'Kani reference for the byte at offset i of the checkpoint body; the frozen function crates/aspis-r1-cost-probe/src/verifier.rs:325 checkpoint builds the whole vector; no frozen per-byte function. A spec-versus-implementation theorem would be new work, not a fresh=gate equality.',
 'encode_k':'wrapper with a Kani contract around frozen QM31::write_le_bytes (crates/aspis-core/src/field.rs:1028); the wrapper is a tools-crate function; its callee has a frozen definition (aspis-core emission PCWM_E001 is relevant)',
 'e_byte':'reference accessor on WideExact limbs; related frozen: WideExact::to_limbs (aspis-core/src/field/wide_exact.rs:238), to_le_bytes (:273); no frozen function of this shape',
 'k_byte':'reference accessor over encode_k; no frozen function of this shape',
 'k_from_limbs':'struct literal of QM31/CM31/M31 from four limbs; no frozen function (no QM31::from_limbs in aspis-core at the pin)',
 'word_spec':'little-endian word specification written for the Kani contract; no frozen function',
 'decode_k_spec':'specification of QM31::from_le_bytes (canonicality bound 0x7fffffff); spec only, no frozen function; frozen decoder QM31::from_le_bytes field.rs:1022',
 'decode_e_spec':'specification of WideExact::from_le_bytes; spec only, no frozen function'}
for k,v in rel.items():
    keys[OP+'|OraclePortCkptAbi2Extracted.'+k]['note']=v
keys_final={}
for k,v in keys.items():
    mod=k.split('|')[0]
    cls='COUNTERPART_FOUND_REPORTED_TO_LEAD' if v['relation']=='COUNTERPART_FOUND' else ('GATE_SIDE_LOOP_CLEARED_ONLY_THROUGH_PARENT' if v['relation'].startswith('GATE_SIDE') else 'NO_FROZEN_COUNTERPART')
    v['class']=cls; v['status']='OPEN'
    if mod==OP: v['also']='WRONG_BASIS (P5 emission of unknown configuration) retained from PCWM_'
    keys_final[k]=v
out=dict(schema='PCWR_COUNTERPARTS/1',target_established=False,frozen_pin=PIN,pool_pin='b936275465600469312d1f058cdc91ea2a11f3dc',
 job='PCWR_ item 2 (triage only; no equality work started, no scope used)',search_performed=search,keys=keys_final,
 summary=dict(S8OwnedP6_Funs='4 keys have frozen counterparts (check_values_owned, finish_owned, residue_owned, value_owned) at crates/aspis-r1-cost-probe/src/{compact.rs:139,verifier.rs:226,235,222}; 4 keys are gate-side loop items of two of them. Report to lead for a WAdm-style job; nothing proved here.',
   OraclePort='8 of 8 NO_FROZEN_COUNTERPART (tools-crate Kani specs and reference accessors); stay OPEN; encode_k and body_byte have related frozen callees/functions named in the notes; WRONG_BASIS retained'),
 rows_served_by_module_in_PCXD_ROW_TABLES=rows,
 rows_note='rows of prov-p6r-20261110/PCXD_ROW_TABLES.json row_to_module_to_definitions that reach the module (30 and 33). PCXH_ROW_TABLES.json (599-view) carries per-row verdicts and settled/not-settled counts without module names, so the module-to-row list is taken from PCXD (same 599 rows). Of these, 25 and 31 rows still list the module in open_modules.')
json.dump(out,open('PCWR_COUNTERPARTS.json','w'),indent=1); print(len(keys_final))
