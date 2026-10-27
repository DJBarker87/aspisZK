import JFs_TX2_TailQM
import JFs_TX2_RawMap
set_option autoImplicit false
noncomputable section
namespace AspisR1.JFs_TX2_CheckedQ
open Aeneas Aeneas.Std Result
open JFs_TX2_RawMap

def value (q : FIo_Native.aspis_core.field.QM31) : FIo_Native.fast_pairing.canonical.Q :=
  pack q.c0.a q.c0.b q.c1.a q.c1.b

theorem source (q : FIo_Native.aspis_core.field.QM31) (hq : FIo_QMValues.Canon q) :
    FIo_Native.fast_pairing.checked_q q=ok (.Ok (value q)) := by
  have h0 : q.c0.a<FIo_Native.fast_pairing.canonical.P := by
    unfold FIo_Native.fast_pairing.canonical.P
    have h:=hq.1.1
    scalar_tac
  have h1 : q.c0.b<FIo_Native.fast_pairing.canonical.P := by
    unfold FIo_Native.fast_pairing.canonical.P
    have h:=hq.1.2
    scalar_tac
  have h2 : q.c1.a<FIo_Native.fast_pairing.canonical.P := by
    unfold FIo_Native.fast_pairing.canonical.P
    have h:=hq.2.1
    scalar_tac
  have h3 : q.c1.b<FIo_Native.fast_pairing.canonical.P := by
    unfold FIo_Native.fast_pairing.canonical.P
    have h:=hq.2.2
    scalar_tac
  have r0 : Array.index_usize (value q) 0#usize=ok q.c0.a := rfl
  have r1 : Array.index_usize (value q) 1#usize=ok q.c0.b := rfl
  have r2 : Array.index_usize (value q) 2#usize=ok q.c1.a := rfl
  have r3 : Array.index_usize (value q) 3#usize=ok q.c1.b := rfl
  unfold FIo_Native.fast_pairing.checked_q
  change (do let o ← FIo_Native.fast_pairing.canonical.Q.from_limbs (value q)
             match o with | none => ok (core.result.Result.Err ()) | some v => ok (core.result.Result.Ok v))=_
  simp only [FIo_Native.fast_pairing.canonical.Q.from_limbs,r0,r1,r2,r3,bind_tc_ok,
    if_pos h0,if_pos h1,if_pos h2,if_pos h3]
  rfl

#print axioms source
end AspisR1.JFs_TX2_CheckedQ
end
