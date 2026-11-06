import NKJ_Root
import NGA_CanonicalInjective
import ExtractedMaskQM31Exact
set_option autoImplicit false
namespace NKJ_Cohort
open Aeneas Aeneas.Std Result AspisR1SelectedMaskProbe
abbrev Q := NGA_Cache.Q
abbrev Canon := NGA_Cache.Canonical
abbrev decode := AspisR1.ExtractedMaskQM31Exact.decode
abbrev Input := NGA_PreparePairs.Input

def zero : Q := ⟨⟨0#u32,0#u32⟩,⟨0#u32,0#u32⟩⟩

/-- Pure adopted field operations, at the SAME input pairs. This also pins
lazy-channel evaluation to complete emitted QM31 multiplication/addition Results. -/
def run : List Input → Result Q
 | [] => ok zero
 | x::xs => do
   let p ← field.QM31.mul x.1 x.2
   let tail ← run xs
   field.QM31.add p tail

theorem value (xs : List Input)
 (domain : ∀ x∈xs, Canon x.1 ∧ Canon x.2) :
 ∃ out, run xs=ok out ∧ Canon out ∧ decode out=NGA_SumAlgebra.sumProducts xs := by
 induction xs with
 | nil =>
  refine ⟨zero,rfl,⟨⟨by change (0:Nat)<2147483647;norm_num,by change (0:Nat)<2147483647;norm_num⟩,⟨by change (0:Nat)<2147483647;norm_num,by change (0:Nat)<2147483647;norm_num⟩⟩,?_⟩
  apply QuadraticAlgebra.ext <;> apply QuadraticAlgebra.ext <;>
    simp [zero,decode,AspisR1.ExtractedMaskQM31Exact.decode,NGA_SumAlgebra.sumProducts]
 | cons x xs ih =>
  obtain ⟨hl,hr⟩ := domain x (by simp)
  obtain ⟨p,hp,cp,vp⟩ := AspisR1.ExtractedMaskQM31Exact.current_qm_mul_exact x.1 x.2 hl hr
  obtain ⟨tail,ht,ct,vt⟩ := ih (by intro y hy;exact domain y (by simp [hy]))
  obtain ⟨out,ho,co,vo⟩ := AspisR1.ExtractedMaskQM31Exact.current_qm_add_exact p tail cp ct
  refine ⟨out,by simp only [run,hp,ht,ho,bind_tc_ok],co,?_⟩
  change decode out=decode p+decode tail at vo
  change decode p=decode x.1*decode x.2 at vp
  rw [vo,vp,vt]
  rfl

theorem injective (x y : Q) (hx : Canon x) (hy : Canon y) (h : decode x=decode y) : x=y := by
 have h00 := congrArg (fun z : AspisV8R15.ExactTowerBase.QM31Exact => z.re.re) h
 have h01 := congrArg (fun z : AspisV8R15.ExactTowerBase.QM31Exact => z.re.im) h
 have h10 := congrArg (fun z : AspisV8R15.ExactTowerBase.QM31Exact => z.im.re) h
 have h11 := congrArg (fun z : AspisV8R15.ExactTowerBase.QM31Exact => z.im.im) h
 exact congrArg₂ field.QM31.mk
  (congrArg₂ field.CM31.mk (NGA_CanonicalInjective.word _ _ hx.1.1 hy.1.1 h00) (NGA_CanonicalInjective.word _ _ hx.1.2 hy.1.2 h01))
  (congrArg₂ field.CM31.mk (NGA_CanonicalInjective.word _ _ hx.2.1 hy.2.1 h10) (NGA_CanonicalInjective.word _ _ hx.2.2 hy.2.2 h11))

theorem source (xs : List Input) (arity : xs.length≤4)
 (domain : ∀ x∈xs, Canon x.1 ∧ Canon x.2) :
 NKJ_NativeSmall.run xs=run xs := by
 obtain ⟨out,ho,co,vo⟩ := NGA_SumAlgebra.source xs arity domain
 obtain ⟨out',ho',co',vo'⟩ := value xs domain
 have same : out=out' := injective out out' co co' (vo.trans vo'.symm)
 rw [NKJ_NativeSmall.value xs arity domain,ho,ho',same]
#print axioms value
#print axioms injective
#print axioms source
end NKJ_Cohort
