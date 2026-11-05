"""Deterministic, read-only packet parameter insertion into retained emission."""
from pathlib import Path
import subprocess,re,json,hashlib
E=Path(__file__).resolve().parent
path='evidence/port17release-20261024/dependency-source/S1SemanticCodeBeginV1.lean'
rev='307d36e829c'
src=subprocess.check_output(['git','show',rev+':'+path],text=True)
(E/'NHG_BEGIN_EMISSION_PINS.json').write_text(json.dumps(dict(source_path=path,revision=rev,sha256=hashlib.sha256(src.encode()).hexdigest(),rule='read-only emission, deterministic packet parameter insertion; no extraction rerun'),indent=1))
for i,name in enumerate(['begin13','begin9','begin5','begin']):
 start=re.search(r'^def '+name+r'\s',src,re.M).start();m=re.search(r'^def |^#print',src[start+1:],re.M);end=start+1+m.start()
 body=src[start:end].strip()
 body=body.replace('{H : Type}', '{H : Type} (packet : aspis_core.Digest32 H → r1_wire.SemanticTranscript H → r1_wire.ValidatedRecord → Code ((core.result.Result aspis_core.field.QM31 r1_wire.Error) × r1_wire.SemanticTranscript H))',1)
 body=re.sub(r'\bsemanticValidated\b','packet',body)
 for callee in ['begin13','begin9','begin5']:
  if callee!=name:body=re.sub(r'\b'+callee+r'(?=\s+aspis_coreDigest32Inst)',callee+' packet',body)
 imports='NHG_Lengths' if i==0 else 'NHG_'+['Begin13','Begin9','Begin5'][i-1]
 args=' prefix1 transcript' if name=='begin' else ' prefix1 transcript val val1 val2 valN back'
 params='' if name=='begin' else ''' (val val1 val2 valN : aspis_core.field.QM31)
 (back : aspis_core.field.QM31 → Array aspis_core.field.QM31 10#usize)'''
 theorem=f'''
theorem source {{H : Type}} (D : aspis_core.Digest32 H)
 (prefix1 : r1_wire.Prefix) (transcript : r1_wire.SemanticTranscript H){params} :
 {name} S1SemanticCode.semanticValidated D{args}=
 S1SemanticCode.{name} D{args} := by
 rfl
#print axioms source
'''
 module=['NHG_Begin13','NHG_Begin9','NHG_Begin5','NHG_Begin'][i]
 (E/(module+'.lean')).write_text('import '+imports+'\nset_option autoImplicit false\nopen Aeneas Aeneas.Std Result AspisR1PublicPreparation\nopen AspisR1PublicPreparation.PreparedHashCode (Code)\nnamespace AspisR1.NHG_BeginPackets\n'+body+'\nend AspisR1.NHG_BeginPackets\nnamespace AspisR1.'+module+'\nopen AspisR1.NHG_BeginPackets\n'+theorem+'end AspisR1.'+module+'\n')
