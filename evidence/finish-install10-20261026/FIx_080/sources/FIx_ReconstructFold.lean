import FIx_ReconstructTraversal
set_option autoImplicit false
noncomputable section
namespace AspisR1.FIx_ReconstructFold
open Aeneas Aeneas.Std Result
open FIv_NativeArithmetic (NQ)
open FIv_NativeValue (K Canon decode)
open FIx_ReconstructTraversal (fold slice)
open FIx_ReconstructStep (Capture)

def model (xs : List NQ) (acc : K) : K :=
  (xs.reverse.map decode).foldl (fun a b=>(a+a)+b) acc

theorem value (xs : List NQ) (bound : xs.length≤Usize.max) (acc out : NQ) (c : Capture)
    (hc : ∀ x∈xs,Canon x) (ha : Canon acc)
    (success : fold ⟨slice xs bound,0⟩ acc c=ok out) :
    Canon out ∧ decode out=model xs (decode acc) := by
  induction xs using List.reverseRecOn generalizing acc with
  | nil =>
    rw [FIx_ReconstructTraversal.nil] at success
    have same := Result.ok.inj success
    subst out
    exact ⟨ha,rfl⟩
  | append_singleton xs x ih =>
    rw [FIx_ReconstructTraversal.append] at success
    obtain ⟨⟨next,c'⟩,hnext,tail⟩ := FIv_Map.bind_success _ _ _ success
    have hx := hc x (by simp)
    have v := FIx_ReconstructStep.value c c' acc x next ha hx hnext
    have same := v.2.2
    subst c'
    have rest := ih (by have h:=bound;simp only [List.length_append,List.length_singleton] at h;omega)
      next (by intro y hy;exact hc y (by simp [hy])) v.1 tail
    refine ⟨rest.1,?_⟩
    rw [rest.2,v.2.1]
    simp only [model,List.reverse_append,List.reverse_singleton,List.map_append,List.map_singleton,
      List.singleton_append,List.foldl_cons]
#print axioms value
end AspisR1.FIx_ReconstructFold
end
