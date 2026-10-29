from pathlib import Path
import json,subprocess
D=Path(__file__).parent
m='PV_DIAG9_Encoders';s='''import PV_DIAG9_Result
import R1Z.PV_RunJoin_CallerSuccess43
import R1Z.PV_RunJoin_SemanticComplete40
import R1Z.PV_RunJoin_EncodedComplete41
set_option autoImplicit false
noncomputable section
namespace PV_DIAG9
open Aeneas Aeneas.Std Result R1Z ProverRwFull
variable [ExternalTypes]
'''
steps=[('encoded_slice_no_panic','''theorem encoded_slice_no_panic (ops : ExternalFuns)
 (values : Slice aspis_core.field.wide_exact.WideExact)
 (room : 32*values.length≤Usize.max) :
 @prover.encoded_slice _ (ProverRwP6BodyCandidate.selected ops) values ≠ .fail .panic := by
 obtain ⟨next,h,_,_⟩ := PV_RunJoin_EncodedComplete41.encode ops values room
 exact ok_excludes_panic h'''),
('encoded_slice_no_divergence','''theorem encoded_slice_no_divergence (ops : ExternalFuns)
 (values : Slice aspis_core.field.wide_exact.WideExact)
 (room : 32*values.length≤Usize.max) :
 @prover.encoded_slice _ (ProverRwP6BodyCandidate.selected ops) values ≠ .div := by
 obtain ⟨next,h,_,_⟩ := PV_RunJoin_EncodedComplete41.encode ops values room
 exact ok_excludes_div h'''),
('semantic_domain_no_panic','''theorem semantic_domain_no_panic (ops : ExternalFuns) (logical : Slice U8)
 (out : alloc.vec.Vec U8) (records : List (List U8)) (length : logical.length=13831)
 (domain : PV_RunJoin_SemanticDomain40.Domain ops logical 27#u8 32#usize 0#u8 records)
 (room : out.length+32+records.flatten.length≤Usize.max) :
 @host_compact.compact_semantic _ (ProverRwP6BodyCandidate.selected ops) logical out ≠ .fail .panic := by
 obtain ⟨next,h,_⟩ := PV_RunJoin_SemanticComplete40.encode ops logical out records length domain room
 exact ok_excludes_panic h'''),
('semantic_domain_no_divergence','''theorem semantic_domain_no_divergence (ops : ExternalFuns) (logical : Slice U8)
 (out : alloc.vec.Vec U8) (records : List (List U8)) (length : logical.length=13831)
 (domain : PV_RunJoin_SemanticDomain40.Domain ops logical 27#u8 32#usize 0#u8 records)
 (room : out.length+32+records.flatten.length≤Usize.max) :
 @host_compact.compact_semantic _ (ProverRwP6BodyCandidate.selected ops) logical out ≠ .div := by
 obtain ⟨next,h,_⟩ := PV_RunJoin_SemanticComplete40.encode ops logical out records length domain room
 exact ok_excludes_div h''')]
# Derive the exact Domain from actual caller output; remaining room is stated, not silently inferred.
b='docs/research/v8-r0-zk-20261009/lean/R1Z/PV_RunJoin_CallerSuccess43.lean'
a=subprocess.check_output(['git','show','codex/pv-runjoin-20261026:'+b],text=True)
sig=a[a.index('theorem success'):a.index(' :\n    built.bytes')]
sig=sig.replace('theorem success','theorem actual_caller_encoder_no_panic')
sig+=''' (out : alloc.vec.Vec U8)
 (space : ∀ records, PV_RunJoin_SemanticDomain40.Domain ops (alloc.vec.Vec.deref built.bytes)
  27#u8 32#usize 0#u8 records → out.length+32+records.flatten.length≤Usize.max) :
 @host_compact.compact_semantic _ (ProverRwP6BodyCandidate.selected ops)
  (alloc.vec.Vec.deref built.bytes) out ≠ .fail .panic := by
 obtain ⟨length,records,domain⟩ := PV_RunJoin_CallerSuccess43.success ops hash helperInst commitInst
  public1 c1 d g padding helper commitments initialHash variant built nextCommitments h
 exact semantic_domain_no_panic ops _ out records length domain (space records domain)
'''
s=''.join([s,'abbrev Q := aspis_core.field.QM31\n'])
steps.append(('actual_caller_encoder_no_panic',sig))
cs=[]
for n,d in steps:s+=d+'\n#print axioms '+n+'\n';cs.append(s+'end PV_DIAG9\n')
j=json.loads((D/'plans.json').read_text());j[m]=cs;(D/'plans.json').write_text(json.dumps(j,indent=2)+'\n');(D/(m+'.lean')).write_text(cs[-1])
