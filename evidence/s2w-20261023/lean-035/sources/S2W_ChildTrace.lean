import S2W_OuterErasure
set_option autoImplicit false
noncomputable section
namespace AspisR1.S2W_ChildTrace
open Aeneas Aeneas.Std Result AdapterRw S2W_Trace

theorem perform_return (ops : Ops) {A : Type} (op : Call A) (value : A)
    (before : Log) (returned : invoke ops op = ok value) :
    run ops (perform op) before = ok (value,before ++ [.returned op value]) := by
  simp only [perform,run,returned,thenResult]

theorem first_return (ops : Ops)
    (public1 : aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public)
    (public_bytes proof : Slice U8) (k : Usize) (checkpoint : alloc.vec.Vec U8)
    (before : Log)
    (returned : ops.op10 (SolanaDigest.Insts.Aspis_coreDigestDigest32 ops)
      public1 public_bytes proof k () none = ok (.Ok checkpoint)) :
    run ops (S2W_Outer.first_decoded ops S2W_Outer.traceEffects
      public1 public_bytes proof k) before =
      ok (.Ok checkpoint,before ++ [.returned
        (.op10 (SolanaDigest.Insts.Aspis_coreDigestDigest32 ops)
          public1 public_bytes proof k () none) (.Ok checkpoint)]) := by
  change thenResult
    (ops.op10 (SolanaDigest.Insts.Aspis_coreDigestDigest32 ops)
      public1 public_bytes proof k () none)
    (fun r => run ops (S2W_Outer.mapError (fun e => perform (.op44 e)) r)
      (before ++ [.returned
        (.op10 (SolanaDigest.Insts.Aspis_coreDigestDigest32 ops)
          public1 public_bytes proof k () none) r])) = _
  rw [returned]
  rfl

#print axioms perform_return
#print axioms first_return
end AspisR1.S2W_ChildTrace
