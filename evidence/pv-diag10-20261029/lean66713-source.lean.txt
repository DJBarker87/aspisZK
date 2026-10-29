import PV_DIAG9_Result
import R1Z.PV_RunJoin_CallerSuccess43
import R1Z.PV_RunJoin_SemanticComplete40
import R1Z.PV_RunJoin_EncodedComplete41
set_option autoImplicit false
noncomputable section
namespace PV_DIAG9
open Aeneas Aeneas.Std Result R1Z ProverRwFull
variable [ExternalTypes]
abbrev Q := aspis_core.field.QM31
theorem encoded_slice_no_panic (ops : ExternalFuns)
 (values : Slice aspis_core.field.wide_exact.WideExact)
 (room : 32*values.length≤Usize.max) :
 @prover.encoded_slice _ (ProverRwP6BodyCandidate.selected ops) values ≠ .fail .panic := by
 obtain ⟨next,h,_,_⟩ := PV_RunJoin_EncodedComplete41.encode ops values room
 exact ok_excludes_panic h
#print axioms encoded_slice_no_panic
theorem encoded_slice_no_divergence (ops : ExternalFuns)
 (values : Slice aspis_core.field.wide_exact.WideExact)
 (room : 32*values.length≤Usize.max) :
 @prover.encoded_slice _ (ProverRwP6BodyCandidate.selected ops) values ≠ .div := by
 obtain ⟨next,h,_,_⟩ := PV_RunJoin_EncodedComplete41.encode ops values room
 exact ok_excludes_div h
#print axioms encoded_slice_no_divergence
theorem semantic_domain_no_panic (ops : ExternalFuns) (logical : Slice U8)
 (out : alloc.vec.Vec U8) (records : List (List U8)) (length : logical.length=13831)
 (domain : PV_RunJoin_SemanticDomain40.Domain ops logical 27#u8 32#usize 0#u8 records)
 (room : out.length+32+records.flatten.length≤Usize.max) :
 @host_compact.compact_semantic _ (ProverRwP6BodyCandidate.selected ops) logical out ≠ .fail .panic := by
 obtain ⟨next,h,_⟩ := PV_RunJoin_SemanticComplete40.encode ops logical out records length domain room
 exact ok_excludes_panic h
#print axioms semantic_domain_no_panic
theorem semantic_domain_no_divergence (ops : ExternalFuns) (logical : Slice U8)
 (out : alloc.vec.Vec U8) (records : List (List U8)) (length : logical.length=13831)
 (domain : PV_RunJoin_SemanticDomain40.Domain ops logical 27#u8 32#usize 0#u8 records)
 (room : out.length+32+records.flatten.length≤Usize.max) :
 @host_compact.compact_semantic _ (ProverRwP6BodyCandidate.selected ops) logical out ≠ .div := by
 obtain ⟨next,h,_⟩ := PV_RunJoin_SemanticComplete40.encode ops logical out records length domain room
 exact ok_excludes_div h
#print axioms semantic_domain_no_divergence
theorem actual_caller_encoder_no_panic (ops : ExternalFuns) {H T1 T2 : Type}
    (hash : aspis_core.digest.Digest32 H)
    (helperInst : core.ops.function.FnOnce T1 (Q × Q)
      (core.result.Result (alloc.vec.Vec Q) r1_wire.Error))
    (commitInst : host_semantic.Commitments T2)
    (public1 : aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public)
    (c1 : Array (alloc.vec.Vec aspis_core.field.M31) 26#usize)
    (d g padding : Array Q 1024#usize) (helper : T1) (commitments : T2)
    (initialHash : H) (variant : transport.Variant)
    (built : host_semantic.BuiltSemantics H) (nextCommitments : T2)
    (h : @host_semantic.build_with_helper_mode _ (ProverRwP6BodyCandidate.selected ops)
      H T1 T2 hash helperInst commitInst public1 c1 d g padding helper commitments initialHash variant=
        .ok (.Ok built,nextCommitments)) (out : alloc.vec.Vec U8)
 (space : ∀ records, PV_RunJoin_SemanticDomain40.Domain ops (alloc.vec.Vec.deref built.bytes)
  27#u8 32#usize 0#u8 records → out.length+32+records.flatten.length≤Usize.max) :
 @host_compact.compact_semantic _ (ProverRwP6BodyCandidate.selected ops)
  (alloc.vec.Vec.deref built.bytes) out ≠ .fail .panic := by
 obtain ⟨length,records,domain⟩ := PV_RunJoin_CallerSuccess43.success ops hash helperInst commitInst
  public1 c1 d g padding helper commitments initialHash variant built nextCommitments h
 exact semantic_domain_no_panic ops _ out records length domain (space records domain)

#print axioms actual_caller_encoder_no_panic
end PV_DIAG9
