import XSa_PointList
open Aeneas Aeneas.Std Result
open XRo_Join_Carriers XRo_Join_ResultTransport XSa_DotRun
set_option autoImplicit false
namespace XSa_ListClaimRaw
def finish (inactive : C.E) (powers : List C.E) : Option (List C.E) → Result (Option C.E)
 | none => ok none
 | some xs => do
   let out ← (powers.zip (inactive::xs)).foldlM XSa_ClaimPairs.addTerm XRy_Powers.zero
   ok (some out)


def outcome : Option C.E → core.result.Result C.E C.Err
 | none => .Err .Parse
 | some out => .Ok out

theorem factor {H : Type} (D : C.D H) (sem : C.Sem H) (s : Slice U8)
 (inactive : C.E) (g : Coeff) (kappa : C.E) (powers : List C.E)
 (hp : XRn_Join_powers kappa 7 XRy_Powers.one=ok powers) :
 XRo_Join_PreparedBoundaries.cachedClaim D sem s inactive g kappa =
 mapR outcome (do
   let xs ← XSa_OptionFold.run (XSa_PointList.step sem s g) (List.range 6) []
   finish inactive powers xs) := by
 unfold XRo_Join_PreparedBoundaries.cachedClaim _root_.verifier.prepared_claim
 simp only [_root_.aspis_core.field.wide_exact.WideExact.ONE,
   _root_.aspis_core.field.wide_exact.WideExact.ZERO,bind_tc_ok]
 have hstep : (fun (parts : Option (List C.E)) (point : Nat) =>
   match parts with
   | none => ok none
   | some parts => do
     let p ← XRn_Join_preparedPart (es sem) s g point
     ok (p.map (fun p => parts++[p]))) =
   XSa_OptionFold.absorb (XSa_PointList.step sem s g) := by
   funext parts point
   cases parts <;> rfl
 have hp' := hp
 unfold XRy_Powers.one at hp'
 rw [hp',bind_tc_ok]
 have hfold := congrArg (fun f => (List.range 6).foldlM f (some ([] : List C.E))) hstep
 rw [hfold]
 rw [←XSa_OptionFold.same]
 simp only [mapR_bind]
 apply congrArg (fun f => XSa_OptionFold.run (XSa_PointList.step sem s g) (List.range 6) [] >>= f)
 intro xs
 cases xs with
 | none => rfl
 | some parts =>
   unfold finish
   simp only [mapR_bind,bind_tc_ok]
   rfl

#print axioms factor
end XSa_ListClaimRaw
