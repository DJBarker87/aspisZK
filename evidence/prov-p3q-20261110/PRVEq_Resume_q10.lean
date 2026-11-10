-- PCVQ_ item (1): the fresh VTop resume (PRVEq_VTop_l1) against the deployed reader's source Port4A_NativeReader.resume, every leaf dependence stated.
import Aeneas
import PRVEq_Tx2Deployed_n1
open Aeneas Aeneas.Std Result ControlFlow Error
set_option autoImplicit false
noncomputable section
namespace PCVQ_Resumeq10
open VTop_Stages VTop_Stages.PRVFresh_VTop_l1 AspisR1

abbrev VErr := AdapterRw.aspis_r1_cost_probe.verifier.Error
abbrev SErr := AspisR1Stage2.verifier.Error

def phi {A : Type} : core.result.Result A SErr → core.result.Result A VErr
  | .Ok v => .Ok v
  | .Err e => .Err (Port3_CheckpointInstall.error e)

/-- The fresh program L is the source program R followed by the nominal error map. -/
@[reducible] def Sim {A : Type} (L : Result (core.result.Result A VErr)) (R : Result (core.result.Result A SErr)) : Prop :=
  L = (R >>= fun o => ok (phi o))

theorem sim_err (e : SErr) {A : Type} : Sim (A := A) (ok (.Err (Port3_CheckpointInstall.error e))) (ok (.Err e)) := rfl
theorem sim_ok {A : Type} (a : A) : Sim (ok (.Ok a)) (ok (.Ok a)) := rfl

theorem sim_bind {α A : Type} (m : Result α) (f : α → Result (core.result.Result A VErr))
    (g : α → Result (core.result.Result A SErr)) (h : ∀ a, m = ok a → Sim (f a) (g a)) :
    Sim (m >>= f) (m >>= g) := by
  unfold Sim
  cases hm : m with
  | ok a => simp only [bind_tc_ok]; exact h a hm
  | fail e => simp only [bind_tc_fail]
  | div => simp only [bind_tc_div]

theorem sim_ite {A : Type} (c : Prop) [Decidable c] {a b : Result (core.result.Result A VErr)}
    {a' b' : Result (core.result.Result A SErr)} (ha : c → Sim a a') (hb : ¬c → Sim b b') :
    Sim (if c then a else b) (if c then a' else b') := by
  by_cases hc : c
  · simp only [hc, if_true]; exact ha hc
  · simp only [hc, if_false]; exact hb hc

theorem sim_try {α B : Type} (r : core.result.Result α SErr)
    (kL : α → Result (core.result.Result B VErr)) (kR : α → Result (core.result.Result B SErr))
    (h : ∀ a, Sim (kL a) (kR a)) :
    Sim (core.result.Result.Insts.CoreOpsTry.branch (phi r) >>= fun cf =>
          match cf with
          | core.ops.control_flow.ControlFlow.Continue v => kL v
          | core.ops.control_flow.ControlFlow.Break res =>
            core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual B
              (core.convert.FromSame VErr) res)
        (core.result.Result.Insts.CoreOpsTry.branch r >>= fun cf =>
          match cf with
          | core.ops.control_flow.ControlFlow.Continue v => kR v
          | core.ops.control_flow.ControlFlow.Break res =>
            core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual B
              (core.convert.FromSame SErr) res) := by
  cases r with
  | Ok a => exact h a
  | Err e => rfl

theorem ite_bind' {α β : Type} (c : Prop) [Decidable c] (a b : Result α) (K : α → Result β) :
    ((if c then a else b) >>= K) = if c then a >>= K else b >>= K := by
  split <;> rfl

/-- Every external or helper the fresh resume reads, tied to the ResumeOps leaf that the deployed reader uses.
Stated with an arbitrary continuation K so that each is a direct rewrite rule. -/
structure Leaves (x : Ext) (ops : AspisR1Stage2.ResumeOps) : Prop where
  size : ∀ v, x.verifier_checkpoint_size v = ops.checkpointSize v
  tag : ∀ v, x.transport_Variant_tag v = ops.tag v
  final : ∀ v, x.transport_Variant_final_len v = ops.finalLen v
  ne : ∀ {T U : Type} {N : Std.Usize} (inst : core.cmp.PartialEq T U),
    x.Slice_Insts_CoreCmpPartialEqArray_ne (N := N) inst = ops.ne inst
  any : ∀ {H : Type} (D : aspis_core.digest.Digest32 H) (it : core.slice.iter.Iter Std.U8),
    x.core_slice_iter_Iter_Insts_CoreIterTraitsIteratorIteratorSharedAT_any
      (verifier.resume.closure.Insts.CoreOpsFunctionFnMutTupleSharedU8Bool D) it () = ops.headerAny it
  raw : ∀ n r, verifier.Reader.raw n r = ops.raw n r
  k : ∀ {B : Type} r (K : core.result.Result aspis_core.field.QM31 VErr × verifier.Reader → Result B),
    (verifier.Reader.k x r >>= K) = (ops.readK r >>= fun p => K (phi p.1, p.2))
  e : ∀ {B : Type} r (K : core.result.Result aspis_core.field.wide_exact.WideExact VErr × verifier.Reader → Result B),
    (verifier.Reader.e x r >>= K) = (ops.readE r >>= fun p => K (phi p.1, p.2))
  validate : ∀ {B : Type} q (K : core.result.Result Unit VErr → Result B),
    (verifier.validate_checkpoint_queries q >>= K) = (ops.validate q >>= fun a => K (phi a))
  sem : ∀ {B : Type} b a (K : core.result.Result (Std.Array aspis_core.field.QM31 10#usize × Std.Usize) VErr → Result B),
    (x.verifier_read_checkpoint_semantic_alpha b a >>= K) = (ops.readSemanticAlpha b a >>= fun r => K (phi r))
  weights : ∀ {B : Type} b a w (K : core.result.Result (alloc.vec.Vec aspis_core.field.QM31 × Std.Usize) VErr → Result B),
    (x.verifier_read_checkpoint_weights b a w >>= K) = (ops.readWeights b a w >>= fun r => K (phi r))
  zero : x.aspis_core_field_QM31_ZERO = ops.zeroK
  filled : ∀ {H B : Type} (D : aspis_core.digest.Digest32 H) (n : Std.Usize) (q : aspis_core.field.QM31)
      (K : core.result.Result (alloc.vec.Vec aspis_core.field.QM31) VErr → Result B),
    (x.aspis_core_r0_heap_filled (aspis_core.field.QM31.Insts.CoreMarkerCopy x) n q >>= fun r =>
      x.core_result_Result_map_err (verifier.resume.closure_1.Insts.CoreOpsFunctionFnOnceTupleErrorError D) r () >>= K)
      = (ops.filled n q >>= fun a => K (phi a))

theorem sub32 (n : Std.Usize) (h : 32 ≤ n.val) :
    (n - 32#usize : Result Std.Usize) = lift (Usize.wrapping_sub n 32#usize) := by
  have spec : WP.spec (n - 32#usize : Result Std.Usize) (fun out => out.val = n.val - 32) :=
    UScalar.sub_spec (by scalar_tac)
  obtain ⟨out, run, value⟩ := WP.spec_imp_exists spec
  have same : out = Usize.wrapping_sub n 32#usize := by
    apply UScalar.eq_of_val_eq
    rw [Usize.wrapping_sub_val_eq]
    have capacity : n.val < UScalar.size .Usize := by
      have := n.hBounds; simpa [UScalar.size_def] using this
    have c32 : 32 < UScalar.size .Usize := by rw [UScalar.size_def]; scalar_tac
    have : (32#usize).val = 32 := by rfl
    rw [value, this]
    omega
  rw [run, same]; rfl

set_option pp.deepTerms.threshold 6 in
set_option maxRecDepth 20000 in
theorem resume_sim (x : Ext) (ops : AspisR1Stage2.ResumeOps) (L : Leaves x ops)
    (sizeBound : ∀ v n, ops.checkpointSize v = ok n → 32 ≤ n.val)
    {H : Type} (D : aspis_core.digest.Digest32 H) (bytes proof public1 : Slice Std.U8)
    (v : transport.Variant) (hash : H) :
    Sim (verifier.resume x D bytes proof public1 v hash)
      (Port4A_NativeReader.resume ops (VTop_Checkpoint.digest D) bytes proof public1 v hash) := by
  unfold verifier.resume Port4A_NativeReader.resume
  simp only [L.size, L.tag, L.ne, L.any, L.raw, L.k, L.e, L.validate, L.sem, L.weights, L.final, L.zero, L.filled,
    core.cmp.impls.PartialEqShared.ne, AspisR1Stage2.slicePartialEq, Slice.Insts.CoreCmpPartialEqArray,
    VTop_Checkpoint.digest]
  refine sim_bind _ _ _ (fun i1 hi1 => ?_)
  refine sim_ite _ (fun _ => ?_) (fun hc => ?_)
  · rfl
  refine sim_bind _ _ _ (fun s _ => ?_)
  refine sim_bind _ _ _ (fun b _ => ?_)
  refine sim_ite _ (fun _ => ?_) (fun _ => ?_)
  · rfl
  refine sim_bind _ _ _ (fun i2 _ => ?_)
  refine sim_bind _ _ _ (fun i3 _ => ?_)
  refine sim_ite _ (fun _ => ?_) (fun _ => ?_)
  · rfl
  refine sim_bind _ _ _ (fun i4 _ => ?_)
  refine sim_ite _ (fun _ => ?_) (fun _ => ?_)
  · rfl
  refine sim_bind _ _ _ (fun i5 _ => ?_)
  refine sim_ite _ (fun _ => ?_) (fun _ => ?_)
  · rfl
  refine sim_bind _ _ _ (fun s1 _ => ?_)
  refine sim_bind _ _ _ (fun i6 _ => ?_)
  refine sim_bind _ _ _ (fun p _ => ?_)
  obtain ⟨b1, it⟩ := p
  refine sim_ite _ (fun _ => ?_) (fun _ => ?_)
  · rfl
  have hlen : 32 ≤ (Slice.len bytes).val := by
    have e : Slice.len bytes = i1 := by
      rw [bne_iff_ne] at hc; exact not_not.mp hc
    rw [e]; exact sizeBound v i1 hi1
  rw [sub32 _ hlen]
  refine sim_bind _ _ _ (fun end1 _ => ?_)
  refine sim_bind _ _ _ (fun s2 _ => ?_)
  refine sim_bind _ _ _ (fun s3 _ => ?_)
  refine sim_bind _ _ _ (fun a _ => ?_)
  refine sim_bind _ _ _ (fun b2 _ => ?_)
  refine sim_ite _ (fun _ => ?_) (fun _ => ?_)
  · rfl
  refine sim_bind _ _ _ (fun s4 _ => ?_)
  refine sim_bind _ _ _ (fun s5 _ => ?_)
  refine sim_bind _ _ _ (fun a1 _ => ?_)
  refine sim_bind _ _ _ (fun b3 _ => ?_)
  refine sim_ite _ (fun _ => ?_) (fun _ => ?_)
  · rfl
  refine sim_bind _ _ _ (fun s6 _ => ?_)
  refine sim_bind _ _ _ (fun s7 _ => ?_)
  refine sim_bind _ _ _ (fun s8 _ => ?_)
  refine sim_bind _ _ _ (fun s9 _ => ?_)
  refine sim_bind _ _ _ (fun a2 _ => ?_)
  unfold Port4A_NativeReader.tail
  refine sim_bind _ _ _ (fun b4 _ => ?_)
  refine sim_ite _ (fun _ => ?_) (fun _ => ?_)
  · rfl
  refine sim_bind _ _ _ (fun p _ => ?_)
  obtain ⟨state, r⟩ := p
  refine sim_bind _ _ _ (fun p _ => ?_)
  obtain ⟨a3, r1⟩ := p
  refine sim_bind _ _ _ (fun p _ => ?_)
  obtain ⟨a4, r2⟩ := p
  refine sim_bind _ _ _ (fun p _ => ?_)
  obtain ⟨r3, r4⟩ := p
  first | (refine sim_try _ _ _ (fun val => ?_)) | (dsimp only; refine sim_try _ _ _ (fun val => ?_))
  refine sim_bind _ _ _ (fun p _ => ?_)
  obtain ⟨r5, r6⟩ := p
  first | (refine sim_try _ _ _ (fun val1 => ?_)) | (dsimp only; refine sim_try _ _ _ (fun val1 => ?_))
  refine sim_bind _ _ _ (fun p _ => ?_)
  obtain ⟨r7, r8⟩ := p
  first | (refine sim_try _ _ _ (fun val2 => ?_)) | (dsimp only; refine sim_try _ _ _ (fun val2 => ?_))
  refine sim_bind _ _ _ (fun p _ => ?_)
  obtain ⟨r9, r10⟩ := p
  first | (refine sim_try _ _ _ (fun val3 => ?_)) | (dsimp only; refine sim_try _ _ _ (fun val3 => ?_))
  refine sim_bind _ _ _ (fun p _ => ?_)
  obtain ⟨r11, r12⟩ := p
  first | (refine sim_try _ _ _ (fun val4 => ?_)) | (dsimp only; refine sim_try _ _ _ (fun val4 => ?_))
  refine sim_bind _ _ _ (fun p _ => ?_)
  obtain ⟨a5, r13⟩ := p
  refine sim_bind _ _ _ (fun i8 _ => ?_)
  refine sim_bind _ _ _ (fun p _ => ?_)
  obtain ⟨a6, r14⟩ := p
  refine sim_bind _ _ _ (fun i9 _ => ?_)
  refine sim_bind _ _ _ (fun p _ => ?_)
  obtain ⟨a7, r15⟩ := p
  refine sim_bind _ _ _ (fun i10 _ => ?_)
  refine sim_bind _ _ _ (fun p _ => ?_)
  obtain ⟨a8, r16⟩ := p
  refine sim_bind _ _ _ (fun i11 _ => ?_)
  refine sim_bind _ _ _ (fun p _ => ?_)
  obtain ⟨a9, r17⟩ := p
  refine sim_bind _ _ _ (fun i12 _ => ?_)
  refine sim_bind _ _ _ (fun p _ => ?_)
  obtain ⟨a10, r18⟩ := p
  refine sim_bind _ _ _ (fun i13 _ => ?_)
  refine sim_bind _ _ _ (fun p _ => ?_)
  obtain ⟨a11, r19⟩ := p
  refine sim_bind _ _ _ (fun i14 _ => ?_)
  refine sim_bind _ _ _ (fun p _ => ?_)
  obtain ⟨a12, r20⟩ := p
  refine sim_bind _ _ _ (fun i15 _ => ?_)
  refine sim_bind _ _ _ (fun p _ => ?_)
  obtain ⟨a13, r21⟩ := p
  refine sim_bind _ _ _ (fun i16 _ => ?_)
  refine sim_bind _ _ _ (fun p _ => ?_)
  obtain ⟨a14, r22⟩ := p
  refine sim_bind _ _ _ (fun i17 _ => ?_)
  refine sim_bind _ _ _ (fun p _ => ?_)
  obtain ⟨a15, r23⟩ := p
  refine sim_bind _ _ _ (fun i18 _ => ?_)
  refine sim_bind _ _ _ (fun p _ => ?_)
  obtain ⟨a16, r24⟩ := p
  refine sim_bind _ _ _ (fun i19 _ => ?_)
  refine sim_bind _ _ _ (fun p _ => ?_)
  obtain ⟨a17, r25⟩ := p
  refine sim_bind _ _ _ (fun i20 _ => ?_)
  refine sim_bind _ _ _ (fun p _ => ?_)
  obtain ⟨a18, r26⟩ := p
  refine sim_bind _ _ _ (fun i21 _ => ?_)
  refine sim_bind _ _ _ (fun p _ => ?_)
  obtain ⟨a19, r27⟩ := p
  refine sim_bind _ _ _ (fun i22 _ => ?_)
  refine sim_bind _ _ _ (fun p _ => ?_)
  obtain ⟨a20, r28⟩ := p
  refine sim_bind _ _ _ (fun i23 _ => ?_)
  refine sim_bind _ _ _ (fun p _ => ?_)
  obtain ⟨a21, r29⟩ := p
  refine sim_bind _ _ _ (fun i24 _ => ?_)
  refine sim_bind _ _ _ (fun p _ => ?_)
  obtain ⟨a22, r30⟩ := p
  refine sim_bind _ _ _ (fun i25 _ => ?_)
  refine sim_bind _ _ _ (fun p _ => ?_)
  obtain ⟨a23, r31⟩ := p
  refine sim_bind _ _ _ (fun i26 _ => ?_)
  refine sim_bind _ _ _ (fun p _ => ?_)
  obtain ⟨a24, r32⟩ := p
  refine sim_bind _ _ _ (fun i27 _ => ?_)
  refine sim_bind _ _ _ (fun p _ => ?_)
  obtain ⟨a25, r33⟩ := p
  refine sim_bind _ _ _ (fun i28 _ => ?_)
  refine sim_bind _ _ _ (fun p _ => ?_)
  obtain ⟨a26, r34⟩ := p
  refine sim_bind _ _ _ (fun i29 _ => ?_)
  refine sim_bind _ _ _ (fun r35 _ => ?_)
  first | (refine sim_try _ _ _ (fun _u => ?_)) | (dsimp only; refine sim_try _ _ _ (fun _u => ?_))
  refine sim_bind _ _ _ (fun r36 _ => ?_)
  first | (refine sim_try _ _ _ (fun val5 => ?_)) | (dsimp only; refine sim_try _ _ _ (fun val5 => ?_))
  obtain ⟨semantic_alpha, at1⟩ := val5
  refine sim_bind _ _ _ (fun p _ => ?_)
  obtain ⟨r37, r38⟩ := p
  first | (refine sim_try _ _ _ (fun val6 => ?_)) | (dsimp only; refine sim_try _ _ _ (fun val6 => ?_))
  refine sim_bind _ _ _ (fun p _ => ?_)
  obtain ⟨r39, r40⟩ := p
  first | (refine sim_try _ _ _ (fun val7 => ?_)) | (dsimp only; refine sim_try _ _ _ (fun val7 => ?_))
  refine sim_bind _ _ _ (fun p _ => ?_)
  obtain ⟨r41, r42⟩ := p
  first | (refine sim_try _ _ _ (fun val8 => ?_)) | (dsimp only; refine sim_try _ _ _ (fun val8 => ?_))
  refine sim_bind _ _ _ (fun p _ => ?_)
  obtain ⟨r43, r44⟩ := p
  first | (refine sim_try _ _ _ (fun val9 => ?_)) | (dsimp only; refine sim_try _ _ _ (fun val9 => ?_))
  refine sim_bind _ _ _ (fun p _ => ?_)
  obtain ⟨r45, r46⟩ := p
  first | (refine sim_try _ _ _ (fun val10 => ?_)) | (dsimp only; refine sim_try _ _ _ (fun val10 => ?_))
  refine sim_bind _ _ _ (fun p _ => ?_)
  obtain ⟨r47, r48⟩ := p
  first | (refine sim_try _ _ _ (fun val11 => ?_)) | (dsimp only; refine sim_try _ _ _ (fun val11 => ?_))
  refine sim_bind _ _ _ (fun p _ => ?_)
  obtain ⟨r49, r50⟩ := p
  first | (refine sim_try _ _ _ (fun val12 => ?_)) | (dsimp only; refine sim_try _ _ _ (fun val12 => ?_))
  refine sim_bind _ _ _ (fun i30 _ => ?_)
  refine sim_bind _ _ _ (fun q _ => ?_)
  refine sim_bind _ _ _ (fun r52 _ => ?_)
  first | (refine sim_try _ _ _ (fun val13 => ?_)) | (dsimp only; refine sim_try _ _ _ (fun val13 => ?_))
  refine sim_bind _ _ _ (fun r53 _ => ?_)
  first | (refine sim_try _ _ _ (fun val14 => ?_)) | (dsimp only; refine sim_try _ _ _ (fun val14 => ?_))
  obtain ⟨weights, at2⟩ := val14
  refine sim_ite _ (fun _ => ?_) (fun _ => ?_)
  · rfl
  refine sim_bind _ _ _ (fun i31 _ => ?_)
  rfl
#print axioms resume_sim
end PCVQ_Resumeq10
