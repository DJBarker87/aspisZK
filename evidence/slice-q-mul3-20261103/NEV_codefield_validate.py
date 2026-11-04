"""Small outside-slice dependency gate, not an extra slice row."""
from pathlib import Path
import json,copy,hashlib,re,sys
sys.dont_write_bytecode=True
from NEV_composition import own_native,gate
E=Path(__file__).resolve().parent;R=E.parent.parent
obj=lambda p:json.loads(Path(p).read_text())
sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
def validate():
 target='verifier::NEV_row_step::codefield_m31_lift'
 p=own_native('NEV_K030',0,target);n=own_native('NEV_K031',1,target)
 assert p['source_hashes']==n['source_hashes'] and p['native_command']==n['native_command']
 pe=copy.deepcopy(p['env']);ne=copy.deepcopy(n['env'])
 assert ne.pop('RUSTFLAGS')==pe.pop('RUSTFLAGS')+' --cfg NEV_wrong_lift' and pe==ne
 for suffix in ['-graph-check.json','-tool-check.json']:
  assert obj(E/('NEV_K030'+suffix))==obj(E/('NEV_K031'+suffix))
 for d in [p,n]:
  assert d['copy_patch_sha256']==gate.KMX
  assert sha(R/'evidence/kani-mitig-20261028/KMX_copy_stubs.patch')==gate.KMX
  src=(E/d['attempt']/'sources/NEV_src/crates/aspis-r1-cost-probe/src/NEV_row_step.rs').read_text()
  body=src[src.index('// Small documented outside-Q constructor;'):]
  assert body.count('fn codefield_m31_lift()')==1
  assert '<E as aspis_core::r0::CodeField>::from_m31(M31(word)).to_limbs()' in body
  assert 'word%2147483647' in body and 'observed<8' in body
  assert not re.search(r'Option\s*<\s*fn|stub_verified|proof_for_contract|\bstatic\s',body)
 extraction=obj(E/'NEV_E001/NEV_EXTRACTION_PINS.json')
 assert extraction['charon_exit']==extraction['exit']==0
 assert extraction['lock_before']==extraction['lock_after']
 assert extraction['frozen_revision']==gate.F and extraction['actual_core_sources']
 for name,h in extraction['outputs'].items():
  assert sha(E/name)==h
  assert sha(E/name)==sha(E/('NEV_CodeFieldRaw/'+Path(name).name))
 funs=(E/'NEV_CodeFieldRaw/Funs.lean').read_text()
 assert 'FunsExternal' not in funs and not re.search(r'\baxiom\s|\bsorry\b',funs)
 receipts=[]
 for label,theorems in [('NEV_L012',['NEV_CodeFieldBridge.total','NEV_CodeFieldBridge.cohort']),
    ('NEV_L013',['NEV_CodeFieldUse.basis_call']),('NEV_L017',['NEV_CodeFieldPacket.extracted_root'])]:
  c=dict(receipt=str((E/label/'receipt.json').relative_to(R)),receipt_sha256=sha(E/label/'receipt.json'),theorems=theorems)
  for theorem in theorems:gate.neb.check_receipt(c,theorem)
  receipts.append(c)
 return dict(status='CLOSED-CONDITIONAL_AUXILIARY',function='aspis_core::r0::CodeField<WideExact>::from_m31',
  frozen_revision=gate.F,domain='All raw U32 inputs; equality to NBF_RowInstall.embedM on canonical input, derived at the SAME production-basis read',
  native_pair=['NEV_K030','NEV_K031'],extraction='NEV_E001',lean_evidence=receipts,
  remaining_inner_hypotheses=[],slice_rows_closed=[],trust='P6/D188 semantic transport option A retained; compiler/library/runtime/artifact qualifications retained')
if __name__=='__main__':
 result=validate();(E/'NEV_CODEFIELD_PACKET.json').write_text(json.dumps(result,indent=2)+'\n');print(result['status'])
