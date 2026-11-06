from pathlib import Path
import re,json,hashlib
E=Path(__file__).resolve().parent;R=E/'NJG_emitted/verify_finish/raw/NHR_verify_finish'
t=(R/'Types.lean').read_text();f=(R/'Funs.lean').read_text()
items=re.findall(r'^(?:structure|inductive|def)\s+([\w.]+)(?:\s+\(H : Type\))?',t,re.M)
mapping={}
for n in items:
 if 'verify_finish.closure' in n:continue
 dst='AspisR1PublicPreparation.'+n.replace('aspis_statement.pool_v1.','pool_v1.').replace('aspis_core.digest.Digest32','aspis_core.Digest32').replace('aspis_core.state_only_prefix.r0.Challenges','r1_wire.Challenges')
 mapping[n]=dst
aliases='import NIX_CertificateFrames\nset_option autoImplicit false\nnamespace AspisR1.NJG_FinishBody\nopen Aeneas Aeneas.Std Result\n'
for n,dst in mapping.items():aliases+='abbrev '+n+' := '+dst+'\n'
for name,target in [('closure_2','Closure2'),('closure_1','Closure1'),('closure','Closure')]:aliases+=f'abbrev r1_semantic.verify_finish.{name} := AspisR1PublicPreparation.FinishModel.{target}\n'
aliases+='end AspisR1.NJG_FinishBody\n';(E/'NJG_FinishTypes.lean').write_text(aliases)
head='''import NJG_FinishTypes
set_option autoImplicit false
noncomputable section
namespace AspisR1.NJG_FinishBody
open Aeneas Aeneas.Std Result ControlFlow Error
structure Boundaries (H : Type) where
 fromFn : {T F : Type} → (N : Usize) → core.ops.function.FnMut F Usize T → F → Result (Array T N)
 mapError : {T E F O : Type} → core.ops.function.FnOnce O E F → core.result.Result T E → O → Result (core.result.Result T F)
 qEq : aspis_core.field.QM31 → aspis_core.field.QM31 → Result Bool
 pointEq : aspis_core.circle.SecureCirclePoint → aspis_core.circle.SecureCirclePoint → Result Bool
 add : aspis_core.field.QM31 → aspis_core.field.QM31 → Result aspis_core.field.QM31
 mul : aspis_core.field.QM31 → aspis_core.field.QM31 → Result aspis_core.field.QM31
 mask : Array aspis_core.field.QM31 16#usize → Array aspis_core.field.QM31 10#usize → aspis_core.field.QM31 → Array aspis_core.field.QM31 10#usize → Result aspis_core.field.QM31
 terminal : aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public → Array (Array aspis_core.field.QM31 29#usize) 3#usize → Array aspis_core.field.QM31 10#usize → aspis_core.state_only_prefix.r0.Challenges → Result (core.result.Result aspis_core.field.QM31 aspis_core.state_only_prefix.r0.Error)
 claims : r1_wire.Prefix → Result (core.result.Result (Array (Array aspis_core.field.QM31 29#usize) 3#usize) r1_wire.Error)
 rounds : aspis_core.digest.Digest32 H → r1_wire.Prefix → r1_wire.SemanticTranscript H → Result (core.result.Result (aspis_core.field.QM31 × Array aspis_core.field.QM31 10#usize × r1_wire.SemanticTranscript H) r1_wire.Error)
 record : r1_wire.Prefix → U8 → Result (core.result.Result r1_wire.ValidatedRecord r1_wire.Error)
 payload : r1_wire.Prefix → U8 → Result (core.result.Result (Slice U8) r1_wire.Error)
 circle : aspis_core.digest.Digest32 H → r1_wire.SemanticTranscript H → r1_wire.ValidatedRecord → Result (core.result.Result aspis_core.circle.SecureCirclePoint r1_wire.Error × r1_wire.SemanticTranscript H)
 state : aspis_core.digest.Digest32 H → r1_wire.SemanticTranscript H → Result (Array U8 32#usize)
 decode : (N : Usize) → r1_wire.ValidatedRecord → Usize → Result (core.result.Result (Array aspis_core.field.QM31 N) r1_wire.Error)

def qCmp {H : Type} (B : Boundaries H) : core.cmp.PartialEq aspis_core.field.QM31 aspis_core.field.QM31 where
 eq := B.qEq
 ne := core.cmp.PartialEq.ne.trait_default (qCmp B)
'''
# Avoid recursive dictionary: use the existing generic default via an eq-only dictionary
# ne is defined by negating the eq result, exactly the trait-default semantics.
head=head.replace(' ne := core.cmp.PartialEq.ne.trait_default (qCmp B)',' ne := fun a b=>do let equal←B.qEq a b;ok (!equal)')
start=f.index('/-- [aspis_r1_cost_probe::r1_semantic::mark]');body=f[start:];body=body[:body.rindex('end NHR_verify_finish')]
repls={'r1_wire.Error.':'AspisR1PublicPreparation.r1_wire.Error.','aspis_core.field.QM31.Insts.CoreCmpPartialEqQM31':'(qCmp B)','aspis_core.circle.SecureCirclePoint.Insts.CoreCmpPartialEqSecureCirclePoint.eq':'B.pointEq','aspis_core.field.QM31.add':'B.add','aspis_core.field.QM31.mul':'B.mul','aspis_core.state_only_hiding.state_only_selected_mask_value':'B.mask','aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public.terminal_qm31':'B.terminal','r1_semantic.claims':'B.claims','r1_semantic.semantic_rounds':'B.rounds','r1_wire.Prefix.validated_record':'B.record','r1_wire.Prefix.payload':'B.payload','r1_wire.SemanticTranscript.circle_validated':'B.circle','r1_wire.SemanticTranscript.impl.state':'B.state','r1_wire.ValidatedRecord.decode_k':'B.decode','core.array.from_fn':'B.fromFn','core.result.Result.map_err':'B.mapError'}
for a,b in sorted(repls.items(),key=lambda x:-len(x[0])):body=body.replace(a,b)
body=body.replace('def r1_semantic.verify_finish\n  {H : Type}', 'def r1_semantic.verify_finish\n  {H : Type} (B : Boundaries H)')
tail='''
theorem mark_value (obs : Option (verifier.Phase → Result Unit)) (i : U8) : r1_semantic.mark obs i=ok () := rfl
#print axioms mark_value
#print axioms r1_semantic.verify_finish
end AspisR1.NJG_FinishBody
end
'''
(E/'NJG_FinishBody.lean').write_text(head+body+tail)
(E/'NJG_FINISH_PACKAGING.json').write_text(json.dumps(dict(raw_types_sha256=hashlib.sha256(t.encode()).hexdigest(),raw_funs_sha256=hashlib.sha256(f.encode()).hexdigest(),aliases=mapping,external_replacements=repls,scope='namespace/type-alias and explicit dictionary packaging; no raw external axioms imported; no child/native law asserted',removed_generated_instances=['raw QName field Eq impl dictionary replaced by explicit B.qEq dictionary'],source_revision='4bb3b3f51e16b4525f1d10336e2b0bcbbd775387'),indent=2))
print('NJG finish packaging generated without template axioms')
