import R1Z.PDict_SemOracleRecord222
set_option autoImplicit false
noncomputable section
namespace R1Z.PDict_Static222
open Aeneas Aeneas.Std ProverRwFull PDict_FormatterTypeMaps PDict_FormatterDictionaryMap

theorem erase_241 (base : ExternalTypes) (F : Type) (ops : @ExternalFuns base)
    (hw : @PDict_WorkTransport222.WorkExtensional base ops) :
    letI : ExternalTypes := base
    ∀ {H A B T : Type} (digest : aspis_core.digest.Digest32 H)
    (fa : core.ops.function.FnOnce A (aspis_core.field.QM31 × aspis_core.field.QM31)
      (core.result.Result (alloc.vec.Vec aspis_core.field.QM31) r1_wire.Error))
    (fb : core.ops.function.FnOnce B (aspis_core.field.QM31 × aspis_core.field.QM31)
      (core.result.Result (alloc.vec.Vec aspis_core.field.QM31) r1_wire.Error))
    (ci : host_semantic.Commitments T) (public1 : Public)
    (c1 : Array (alloc.vec.Vec aspis_core.field.M31) 26#usize)
    (d g padding : Array aspis_core.field.QM31 1024#usize)
    (a : A) (b : B) (commitments : T) (hash : H) (variant : transport.Variant),
    (∀ l c, fa.call_once a (l,c) = fb.call_once b (l,c)) →
    @host_semantic.build_with_helper_mode (types base F) (selected base F ops) H A T
      digest fa ci (pub base F public1) c1 d g padding a commitments hash variant =
    @host_semantic.build_with_helper_mode base ops H B T
      digest fb ci public1 c1 d g padding b commitments hash variant := by
  intro H A B T digest fa fb ci public1 c1 d g padding a b commitments hash variant hab
  delta host_semantic.build_with_helper_mode
  delta host_semantic.build_with_helper_mode.match_1
  simp only [erase_60 base F ops, erase_136 base F ops, erase_148 base F ops,
    erase_149 base F ops, erase_165 base F ops, erase_169 base F ops,
    erase_173 base F ops, erase_179 base F ops, erase_182 base F ops,
    erase_189 base F ops, erase_195 base F ops, erase_160 base F ops,
    erase_204 base F ops, erase_207 base F ops, erase_239 base F ops,
    erase_240 base F ops, erase_203 base F ops, PDict_PublicLeaves222.bytes,
    semantic_sumcheck_record base F ops hw digest, hab]
  rfl

#print axioms erase_241
end R1Z.PDict_Static222
