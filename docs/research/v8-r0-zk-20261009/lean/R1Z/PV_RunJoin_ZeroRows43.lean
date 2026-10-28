import R1Z.PV_RunJoin_ZeroShapes43
import R1Z.PV_RunJoin_ByteExtension43
import R1Z.PV_RunJoin_MergeLoop35
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_ZeroRows43
open Aeneas Aeneas.Std Result ProverRwFull PV_RunJoin_ResultPost41 PV_RunJoin_ByteExtension43
variable [ExternalTypes]
abbrev Q := aspis_core.field.QM31

def Good {H : Type} (out : alloc.vec.Vec U8) (n : Nat)
    (next : host_wire.SemanticTranscript H × alloc.vec.Vec U8 × Array Q 10#usize ×
      Option (core.result.Result (Array Q 10#usize) r1_wire.Error)) : Prop :=
  match next.2.2.2 with
  | some (.Err _) => True
  | _ => Ext out.val next.2.1.val (5*n)

theorem loop (ops : ExternalFuns) {H : Type} (hash : aspis_core.digest.Digest32 H)
    (n : Nat) (i : Usize) (transcript : host_wire.SemanticTranscript H)
    (out : alloc.vec.Vec U8) (zc : Array Q 10#usize)
    (bound : i.val+n=10) (room : out.length+5*n≤Usize.max) :
    Post (Good out n) (@host_semantic.zc_rows_loop _ (ProverRwP6BodyCandidate.selected ops)
      H hash transcript out zc i) := by
  induction n generalizing i transcript out zc with
  | zero =>
    unfold host_semantic.zc_rows_loop
    rw [ProverRw19LoopBind.loop_bind]
    simp only [host_semantic.zc_rows_loop.body,
      show ¬i<10#usize from (by change ¬i.val<10;omega),↓reduceIte,bind_tc_ok]
    exact PV_RunJoin_ByteExtension43.refl out.val
  | succ n ih =>
    have hi : i<10#usize := by change i.val<10;omega
    have inc := PV_RunJoin_MergeLoop35.increment i (by omega)
    have post := PV_RunJoin_RecordPost43.append ops hash
      (U8.wrapping_add 3#u8 (UScalar.cast .U8 i)) 0#u8 0#usize
      (Array.to_slice (Std.Array.empty U8)) transcript out
      (PV_RunJoin_ZeroShapes43.shape ops i (by omega)) rfl (by omega)
    unfold host_semantic.zc_rows_loop
    rw [ProverRw19LoopBind.loop_bind]
    simp only [host_semantic.zc_rows_loop.body,hi,↓reduceIte,lift,bind_tc_ok]
    apply PV_RunJoin_RecordAppend41.bind_post post
    intro triple hp
    rcases triple with ⟨r,t,o⟩
    cases r with
    | Err e => trivial
    | Ok q =>
      obtain ⟨header,hlen,hbytes,olen⟩ := hp
      have prefix : Ext out.val o.val 5 := by
        refine ⟨header,hlen,?_⟩
        simpa only [List.append_nil] using hbytes
      simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok]
      apply PV_RunJoin_ResultPost41.bind
      intro zc1
      simp only [lift,bind_tc_ok]
      have next := ih (Usize.wrapping_add i 1#usize) t o zc1
        (by rw [inc];omega) (by rw [olen];omega)
      apply PV_RunJoin_RecordAppend41.bind_post next
      intro result hr
      rcases result with ⟨t1,o1,z1,pending⟩
      cases pending with
      | none =>
        change Ext out.val o1.val (5*(n+1))
        have h := PV_RunJoin_ByteExtension43.trans prefix hr
        convert h using 1 <;> omega
      | some status =>
        cases status with
        | Err e => trivial
        | Ok value =>
          change Ext out.val o1.val (5*(n+1))
          have h := PV_RunJoin_ByteExtension43.trans prefix hr
          convert h using 1 <;> omega
#print axioms loop
end R1Z.PV_RunJoin_ZeroRows43
