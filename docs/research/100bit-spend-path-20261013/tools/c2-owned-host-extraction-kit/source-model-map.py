#!/usr/bin/env python3
"""Read/hash audit of source-to-model obligations; never asserts refinement."""
from pathlib import Path
import argparse,hashlib,json,subprocess
ROOT=Path(__file__).resolve().parents[5];HOME=Path(__file__).resolve().parent
sha=lambda b:hashlib.sha256(b).hexdigest()
def main():
 ap=argparse.ArgumentParser();ap.add_argument('--revision',required=True);ap.add_argument('--out',type=Path,required=True);ap.add_argument('--check',action='store_true');a=ap.parse_args()
 rev=subprocess.check_output(['git','-C',str(ROOT),'rev-parse',a.revision]).decode().strip()
 old={}
 for p in [HOME/'input/source-pins.json',HOME/'input-build/source-pins.json']:
  for x in json.loads(p.read_text())['cuts']:old[x['name']]=x
 items={}
 for name,x in old.items():
  raw=subprocess.check_output(['git','-C',str(ROOT),'show',rev+':'+x['path']]);fragment=raw[x['start_byte']:x['end_byte_exclusive']]
  assert sha(fragment)==x['sha256'], ('Source span changed: re-extract/re-map, do not silently omit',name)
  items[name]={'path':x['path'],'start_byte':x['start_byte'],'end_byte_exclusive':x['end_byte_exclusive'],'sha256':sha(fragment),'source_file_sha256':sha(raw),'classification':'unchanged exact selected source slice'}
 mappings=[
  ('copied','backend_c2 / wide_from_qm31 / canonical_qm31','Models the map into owned Wide rows; actual canonicalization is source-pinned. Caller emission remains blocked, and raw-to-exact interpretation is still unbound.'),
  ('coefficients','commitment_build / variant_coefficients / variant_row / coefficient_to_row / transport_order / pad_rows / wide_c0','Models actual variant transport followed by c0 projection, in that order. Operations fields are parameters, not the actual Rust definitions.'),
  ('Operations.checkField','commitment_build / wide_limbs','Explicit primitive outcome for the source upper-limb check. The model does not prove the check from canonicality.'),
  ('Operations.encode','commitment_build / encoding_domain','Each result is an explicit execution boundary. No content/length inferred from type. Actual EncodingDomain::encode correspondence and arithmetic remain open.'),
  ('Operations.buildTree','commitment_build / private_salts / tree','Groups packing/allocation/hash/salt/tree effects as a final callback. This is a conditional model boundary, not an extracted source helper.'),
  ('run / Owned','commitment_build / commitment','Conditional two-lane construction only. Omits initial message/salt-length checks and allocation failures, C1 case, Backend state mutation, and destruction. No actual Rust execution theorem.'),
  ('word / literalMessage / semantic_pair','commitment / word','Indexes the retained encoder result lists with explicit actual-length proofs. toExact is an unbound interpretation boundary. Bytes/root relation, full semantic read and custody not derived.')]
 result={'source_revision':rev,'source_cut_base_revision':json.loads((HOME/'input/source-pins.json').read_text())['revision'],'selected_source_declarations':items,'selected_source_declaration_count':len(items),'model_file':'docs/research/100bit-spend-path-20261013/lean/C2OwnedHostConstruction.lean','model_sha256':sha((ROOT/'docs/research/100bit-spend-path-20261013/lean/C2OwnedHostConstruction.lean').read_bytes()),'mapping':[dict(model=x,source_cuts=y.split(' / '),status=z) for x,y,z in mappings],'actual_source_refinement_status':'OPEN: both actual caller and whole constructor have valid Charon LLBC but failed Aeneas. Conditional model theorem is not checked actual source execution.','omissions':['Backend copy/salt-take/constructor-error state carry remains unproved; no error-state equivalence claim from functional model.','PrivateSalts::Drop volatile erasure/implicit drop effects unmodeled.','Native saved verifier counters are not a full chronological prover+verifier oracle witness.','Packing/salt-path/custody/checkpoint-authentication remain independent obligations.']}
 b=(json.dumps(result,indent=2,sort_keys=True)+'\n').encode()
 if a.check:assert a.out.read_bytes()==b
 else:a.out.parent.mkdir(parents=True,exist_ok=True);a.out.write_bytes(b)
 print(json.dumps({'check':a.check,'source_revision':rev,'count':len(items),'report_sha256':sha(b)}))
if __name__=='__main__':main()
