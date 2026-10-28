import R1Z.PV_DL_EncoderZip
import R1Z.PV_DL_EncoderSelected
open Aeneas Aeneas.Std Result ProverRwFull
namespace R1Z.PV_DL_EncoderNative
set_option autoImplicit false

def run {E : Type} (inst : aspis_core.r0.scalar.CodeField E) :
    List ((E×E)×E) → E → E → Result (E×E)
  | [],p0,p1 => ok (p0,p1)
  | entry::tail,p0,p1 => do
    let (p0,p1) ← PV_DL_EncoderZip.applyEntry inst entry p0 p1
    run inst tail p0 p1

theorem suffix {T : Type} (xs : List T) (j : Nat) (x : T)
    (h : xs[j]?=some x) : xs.drop j=x::xs.drop (j+1) := by
  obtain ⟨hj,hx⟩ := List.getElem?_eq_some_iff.mp h
  rw [List.drop_eq_getElem_cons hj,hx]

theorem fold {E : Type} [Inhabited E] (inst : aspis_core.r0.scalar.CodeField E)
    (q : Array E 1024#usize) (b : Array E 512#usize)
    (fuel : Nat) (j : Usize) (p0 p1 : E) (rank : j.val+fuel=512) :
    PV_DL_EncoderFold.finite inst q b fuel j p0 p1=
      run inst ((PV_DL_EncoderZip.entries q b).drop j.val) p0 p1 := by
  induction fuel generalizing j p0 p1 with
  | zero =>
    have hj : j.val=512 := by omega
    rw [hj,List.drop_eq_nil_of_le (by rw [PV_DL_EncoderZip.count])]
    rfl
  | succ fuel ih =>
    have hj : j.val<512 := by omega
    rw [suffix _ j.val _ (PV_DL_EncoderZip.coordinate q b j.val hj)]
    simp only [PV_DL_EncoderFold.finite,run,PV_DL_EncoderZip.step inst q b j p0 p1 hj]
    apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
    intro pair hp
    rcases pair with ⟨a,c⟩
    simp only [Aeneas.Std.uncurry]
    rw [ih (PV_DL_EncoderRange.advance j) a c (by rw [PV_DL_EncoderRange.advance_val j hj];omega)]
    rw [PV_DL_EncoderRange.advance_val j hj]

/-- The native forward chunks/zip loop, including arbitrary field Result
failures, rather than a selected dictionary equated to itself. -/
def value {E : Type} (inst : aspis_core.r0.scalar.CodeField E)
    (q : Array E 1024#usize) (p : aspis_core.r0.domain.Point E) : Result E := do
  let basis ← PV_DL_EncoderBasis.value inst p.x
  let p0 ← inst.ZERO
  let p1 ← inst.ZERO
  let (p0,p1) ← run inst (PV_DL_EncoderZip.entries q basis) p0 p1
  let product ← inst.mul p.y p1
  inst.add p0 product

theorem source_reference {E : Type} (inst : aspis_core.r0.scalar.CodeField E)
    (q : Array E 1024#usize) (p : aspis_core.r0.domain.Point E) :
    value inst q p=PV_CB_OwnedEncoder.owned.encoder inst q p := by
  letI : Inhabited E := ⟨p.x⟩
  rw [PV_DL_EncoderControl.source_reference]
  unfold value PV_DL_EncoderControl.value
  apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
  intro basis hb
  repeat' (apply (Aeneas.Std.bind_eq_iff _ _ _).mpr;intro x hx)
  rw [fold inst q basis 512 0#usize _ _ (by decide)]
  rfl

/-- Selected op79 consumes the same complete Result as the native structural
interpretation, for arbitrary original field callbacks. -/
theorem selected_native [types : ExternalTypes] (ops : ExternalFuns) {E : Type}
    (inst : aspis_core.r0.scalar.CodeField E) (q : Array E 1024#usize)
    (p : aspis_core.r0.domain.Point E) :
    @aspis_core.r0.encoder.eval_message types (PV_DL_EncoderSelected.selected ops) E inst q p=
      value inst q p := by
  rw [PV_DL_EncoderSelected.consumed,source_reference]

#print axioms selected_native
#print axioms run
#print axioms suffix
#print axioms fold
#print axioms value
#print axioms source_reference
end R1Z.PV_DL_EncoderNative
