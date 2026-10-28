"""Finite consumed-type census, not a generic Drop assertion."""
from pathlib import Path
import hashlib,json,re,subprocess
R=Path(__file__).resolve().parents[2]; E=R/'evidence/pv-fxmem-20261028'
P=Path('docs/research/100bit-spend-path-20261013/lean/prover-rw-20261023')
rows=[]
for p in sorted((R/P).glob('*.lean')):
 s=p.read_text()
 for i,line in enumerate(s.splitlines(),1):
  if re.search(r'\bcore\.mem\.drop\b',line):
   rows.append(dict(path=str(p.relative_to(R)),line=i,text=line.strip(),sha256=hashlib.sha256(p.read_bytes()).hexdigest()))
calls=[x for x in rows if 'abbrev core.mem.drop' not in x['text']]
assert len(calls)==1 and calls[0]['text']=='core.mem.drop level',calls
f=R/P/'ProverRwFullFuns.lean';s=f.read_text();a=s.index('def host_tree.multiproof_levels\n');b=s.index('partial_fixpoint',a)
assert '(level : alloc.vec.Vec Std.U32)' in s[a:b]
assert s[a:b].count('core.mem.drop')==1
rust=R/'crates/aspis-r1-cost-probe/src/host_tree.rs'
assert rust.read_text().splitlines()[28].strip()=='drop(level);'
dictroot=R/'docs/research/v8-r0-zk-20261009/lean/R1Z'
references=[]
for p in sorted(dictroot.glob('PDict*.lean')):
 for i,line in enumerate(p.read_text().splitlines(),1):
  if re.search(r'\bop4\s*:=',line):
   references.append(dict(path=str(p.relative_to(R)),line=i,text=line.strip(),sha256=hashlib.sha256(p.read_bytes()).hexdigest()))
# IOCarriers.op4 is a type field (PathBuf), not a destructor override.
assert len(references)==2 and any('op4 := ops.op4' in x['text'] for x in references),references
j=dict(revision=subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip(),
 complete_emission_occurrences=rows,call_count=1,types=['alloc.vec.Vec Std.U32 = Rust Vec<u32, Global>'],
 source_call=dict(path=str(rust.relative_to(R)),line=29,sha256=hashlib.sha256(rust.read_bytes()).hexdigest()),
 dictionary_op4_assignments=references,
 dictionary_conclusion='PDict_FinalDictionary.selected aliases PDict_Options.selected; its inherited op4 is unchanged. FormatterDictionaryMap explicitly forwards ops.op4; IOCarriers.op4 is ExternalTypes.PathBuf, not ExternalFuns.op4.',
 scope='Explicit op4 invocations only. Implicit Rust drops of other locals are not op4 call sites and are not discharged by this finite row.',
 before='Generic T, arbitrary worlds, fixed callback equals complete native drop Result: refuted and retained.',
 after='Exactly Vec<u32,Global> at host_tree::multiproof_levels; value callback returns ok (); native world consumes vector and frees nonzero-capacity allocation, with zero element destructor calls. Other T and every other ExternalFuns field retained.',
 status='Census checked; source gate, world law and installed callback evidence recorded separately.')
(E/'DROP-INSTANTIATIONS.json').write_text(json.dumps(j,indent=2)+'\n'); print(json.dumps(j,indent=2))
