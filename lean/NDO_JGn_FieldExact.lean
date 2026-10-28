import NDO_JGl_WordProof
import RPv_JFy_FieldTotal
import NDO_JGb_DecodeInjective
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGn_FieldExact
open Aeneas Aeneas.Std Result FIq_Native
open FIv_NativeValue (Canon decode)

theorem add (x y z : field.QM31) (hx : Canon x) (hy : Canon y) (hz : Canon z)
    (value : decode x+decode y=decode z) : field.QM31.add x y=ok z := by
  obtain ⟨out,run,hc,hv⟩ := FIv_PreparedTotal.add x y hx hy
  have same := JGb_DecodeInjective.source out z hc hz (hv.trans value)
  exact same ▸ run
#print axioms add

theorem mul (x y z : field.QM31) (hx : Canon x) (hy : Canon y) (hz : Canon z)
    (value : decode x*decode y=decode z) : field.QM31.mul x y=ok z := by
  obtain ⟨out,run,hc,hv⟩ := JFy_FieldTotal.mul x y hx hy
  have same := JGb_DecodeInjective.source out z hc hz (hv.trans value)
  exact same ▸ run
#print axioms mul

theorem sub (x y z : field.QM31) (hx : Canon x) (hy : Canon y) (hz : Canon z)
    (value : decode x-decode y=decode z) : field.QM31.sub x y=ok z := by
  obtain ⟨out,run,hc,hv⟩ := JFy_FieldTotal.sub x y hx hy
  have same := JGb_DecodeInjective.source out z hc hz (hv.trans value)
  exact same ▸ run
#print axioms sub

theorem bind {α β : Type} (x : Result α) (f : α → Result β) (a : α) (b : β)
    (first : x=ok a) (next : f a=ok b) : (x >>= f)=ok b := by
  rw [first,bind_tc_ok,next]
#print axioms bind
end AspisR1.JGn_FieldExact
end

open Lean Meta Elab Tactic in
run_elab do
  let e ← Elab.Term.elabTerm (← `(Aeneas.Std.Result.ok (1 : Nat) >>= fun n => Aeneas.Std.Result.ok (n+1))) none
  logInfo m!"Bind expression: {e.getAppFn.constName!} / {e.getAppArgs.size}"
