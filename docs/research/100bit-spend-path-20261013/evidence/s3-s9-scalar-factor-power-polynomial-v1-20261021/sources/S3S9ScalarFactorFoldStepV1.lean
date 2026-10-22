import S3S9ScalarFactorActualOpsStepV1

set_option autoImplicit false
open Aeneas Aeneas.Std Result

namespace AspisR1S9ScalarFactorFoldStepV1

abbrev Ops := AspisR1S9HelperP6.FieldOps
abbrev S := AspisR1S9HelperP6.field.WideExact
abbrev Q := AspisR1S9HelperP6.field.QM31
abbrev E := AspisR1CurrentWide.Proof.E

abbrev CanonicalS := AspisR1S9CurrentFieldOpsV1.Canonical
abbrev DecodeS := AspisR1S9CurrentFieldOpsV1.decode

/-- One exact emitted scalar-factor callback step is sound from canonical
inputs. The three array reads remain explicit premises here; range/index
instantiation is a separate small bridge. Field multiplication and addition
are the installed current operations, not assumed success witnesses. -/
theorem scalar_factor_call_mut_step_sound
    (ops : Ops)
    (c : AspisR1S9HelperP6.weights.Weights.scalar_factor.closure)
    (acc pval : S) (qval : Q) (i k : Std.Usize) (z : S)
    (hperm : Array.index_usize AspisR1S9HelperP6.weights.PERM i = .ok k)
    (hp : Array.index_usize c.1 k = .ok pval)
    (hq : Array.index_usize c.2 i = .ok qval)
    (hacc : CanonicalS acc) (hpv : CanonicalS pval)
    (hqv : AspisR1CurrentWide.Proof.CanonicalQM
      (AspisR1S9GeneratedWideMulQM31V2.toQM qval)) :
    (letI : Ops := AspisR1S9ScalarFactorActualOpsStepV1.installActualFactorOps ops
     AspisR1S9HelperP6.weights.Weights.scalar_factor.closure.Insts.CoreOpsFunctionFnMutPairWideExactUsizeWideExact.call_mut
       c (acc, i)) = .ok (z, c) →
      CanonicalS z ∧
      DecodeS z = DecodeS acc +
        ⟨AspisR1CurrentWide.Proof.decodeQM
          (AspisR1S9GeneratedWideMulQM31V2.toQM pval.c0) *
            AspisR1CurrentWide.Proof.decodeQM (AspisR1S9GeneratedWideMulQM31V2.toQM qval),
         AspisR1CurrentWide.Proof.decodeQM
          (AspisR1S9GeneratedWideMulQM31V2.toQM pval.c1) *
            AspisR1CurrentWide.Proof.decodeQM (AspisR1S9GeneratedWideMulQM31V2.toQM qval)⟩ := by
  intro hcall
  cases c with
  | mk p f =>
      letI : Ops := AspisR1S9ScalarFactorActualOpsStepV1.installActualFactorOps ops
      have hdispatch := AspisR1S9ScalarFactorActualOpsStepV1.scalar_factor_call_mut_dispatch
        ops (p, f) (acc, i)
      rw [hdispatch] at hcall
      change (do
        let permIndex ← Array.index_usize AspisR1S9HelperP6.weights.PERM i
        let we ← Array.index_usize p permIndex
        let q ← Array.index_usize f i
        let we1 ← AspisR1S9GeneratedWideMulQM31V2.actualHelperOperation we q
        let we2 ← AspisR1S9CurrentFieldOpsV1.actualWideAdd acc we1
        ok (we2, (p, f))) = .ok (z, (p, f)) at hcall
      rw [hperm] at hcall
      change Array.index_usize p k = .ok pval at hp
      change Array.index_usize f i = .ok qval at hq
      simp only [bind_tc_ok] at hcall
      rw [hp, hq] at hcall
      simp only [bind_tc_ok] at hcall
      cases hmul : AspisR1S9GeneratedWideMulQM31V2.actualHelperOperation pval qval with
      | fail error => simp [hmul] at hcall
      | div => simp [hmul] at hcall
      | ok mulOut =>
          obtain ⟨mulCanon, mulVal⟩ :=
            AspisR1S9GeneratedWideMulQM31V2.actualHelperOperation_success
              pval qval mulOut hpv hqv hmul
          obtain ⟨out, haddTotal, outCanon, outVal⟩ :=
            AspisR1S9CurrentFieldOpsV1.actualWideAdd_total_exact
              acc mulOut hacc mulCanon
          cases hadd : AspisR1S9CurrentFieldOpsV1.actualWideAdd acc mulOut with
          | fail error => simp [hmul, hadd] at hcall
          | div => simp [hmul, hadd] at hcall
          | ok actualOut =>
              have hactual : actualOut = z := by
                simpa [hmul, hadd, bind_tc_ok] using hcall
              have hsame : AspisR1S9CurrentFieldOpsV1.actualWideAdd acc mulOut = .ok out :=
                haddTotal
              rw [hsame] at hadd
              have htotal : out = actualOut := Result.ok.inj hadd
              subst actualOut
              subst z
              constructor
              · exact outCanon
              · change AspisR1S9CurrentFieldOpsV1.decode out = _
                have hmulVal' : AspisR1S9CurrentFieldOpsV1.decode mulOut =
                    ⟨AspisR1CurrentWide.Proof.decodeQM
                        (AspisR1S9GeneratedWideMulQM31V2.toQM pval.c0) *
                      AspisR1CurrentWide.Proof.decodeQM
                        (AspisR1S9GeneratedWideMulQM31V2.toQM qval),
                     AspisR1CurrentWide.Proof.decodeQM
                        (AspisR1S9GeneratedWideMulQM31V2.toQM pval.c1) *
                      AspisR1CurrentWide.Proof.decodeQM
                        (AspisR1S9GeneratedWideMulQM31V2.toQM qval)⟩ := by
                  change AspisR1CurrentWide.Proof.decodeWide
                    (AspisR1S9CurrentFieldOpsV1.toE mulOut) = _
                  have hmap : AspisR1S9CurrentFieldOpsV1.toE mulOut =
                      AspisR1S9GeneratedWideMulQM31V2.toWide mulOut := by
                    cases mulOut with
                    | mk c0 c1 => rfl
                  rw [hmap]
                  exact mulVal
                rw [outVal, hmulVal']

end AspisR1S9ScalarFactorFoldStepV1
