import LIBC_Slices
import LIBC_CheckValuesDomain
import LIB_VCarriers
import NKL_ScanRoot
import RSL_TX1_094
set_option autoImplicit false
noncomputable section
namespace LIBC_CanonicalScan
open Aeneas Aeneas.Std Result AspisR1 RSL
abbrev VErr := LIB_VCarriers.VErr
def Domain (proof : Bytes) : Prop := proof.length=57607
def good (proof : Bytes) : Bool := (NKL_Checks.checks (LIBC_Bytes.raw proof)).all NKL_Checks.test
def value (proof : Bytes) (_ : Env) : Except VErr Unit := if good proof then .ok () else .error .Parse
/-- The CLOSED root's original input domain is retained in the law as well
as Child.dom, so no off-domain successful law may manufacture R4. -/
def law (proof : Bytes) : Spec (Except VErr Unit) := fun env o =>
 Domain proof ∧ o = ⟨.ret (value proof env),[]⟩
def child : Child Bytes (Except VErr Unit) := ⟨Domain,law⟩
theorem returns (proof : Bytes) (env : Env) :
 NND_Returned.Returns (child.law proof) env (value proof env) := by
 intro o r ho hr
 exact LIB_Carriers.graph_returns _ _ env o r ho.2 hr
theorem native_result (proof : Bytes) (h : Domain proof) :
 NJS_Extract.verifier.candidate.canonical_scan
  AspisR1M31Parser.field.M31.from_le_bytes NKL_CanonicalInstallation.childK
  NKL_CanonicalInstallation.childE NKL_CanonicalInstallation.childCV (LIBC_Bytes.raw proof) =
 ok (NKB_CanonicalOpening.reply (good proof)) := by
 have bound : proof.length ≤ Usize.max := by rw [h];scalar_tac
 have width := (LIBC_Bytes.raw_length proof bound).trans h
 rw [NKL_ScanModel.source _ width,←NKL_ScanModel.value _ width]
 rfl
/-- The first source guard is compact_check; all later checks remain in good. -/
theorem first_check (proof : Bytes) (accepted : good proof = true) :
 NFU_Retarget.compact.check_values (NKB_CanonicalPrefix.values (LIBC_Bytes.raw proof)) = ok (.Ok ()) := by
 have member : NKL_Checks.Check.cv (LIBC_Bytes.raw proof) ∈ NKL_Checks.checks (LIBC_Bytes.raw proof) := by
  simp only [NKL_Checks.checks,NKL_Checks.header,List.mem_append,List.mem_cons,List.not_mem_nil,or_false]
  exact Or.inl (Or.inl rfl)
 have checked := (List.all_eq_true.mp accepted) _ member
 change NKL_CanonicalChildren.compactGood (NKB_CanonicalPrefix.values (LIBC_Bytes.raw proof)) = true at checked
 rw [NKL_CanonicalChildren.compact_result,checked]
 rfl
theorem r4_value (proof : Bytes) (env : Env) (ev : List Event)
 (accepted : child.law proof env ⟨.ret (.ok ()),ev⟩) :
 LIBC_CheckValuesDomain.checkValuesDom (slice proof OFF_Y1 OFF_INACTIVE) := by
 obtain ⟨domain,obs⟩ := accepted
 have equality : value proof env = .ok () :=
  (Exit.ret.inj (congrArg Obs.exit obs)).symm
 have pass : good proof = true := by
  cases hg : good proof <;> simp only [value,hg,if_false,if_true,Bool.false_eq_true] at equality ⊢
  · cases equality
  · rfl
 have bound : proof.length ≤ Usize.max := by rw [domain];scalar_tac
 have same := LIBC_Slices.raw_sub proof bound 7031#usize 7495#usize
 change LIBC_Bytes.raw (slice proof OFF_Y1 OFF_INACTIVE) = NKB_CanonicalPrefix.values (LIBC_Bytes.raw proof) at same
 unfold LIBC_CheckValuesDomain.checkValuesDom
 rw [same]
 exact first_check proof pass
theorem r4 (V : VLib) (scan : V.canonicalScan = child)
 (checks : V.checkValuesDom = LIBC_CheckValuesDomain.checkValuesDom) : TX1_094.R4Discharge V := by
 intro proof env ev h
 rw [scan] at h
 rw [checks]
 exact r4_value proof env ev h
#print axioms returns
#print axioms native_result
#print axioms first_check
#print axioms r4_value
#print axioms r4
end LIBC_CanonicalScan
