import FJn_CopyEndpointMap
set_option autoImplicit false
namespace AspisR1.FJn_CopyRowMap
variable {K L : Type} [Field K] [Field L]
def row (f : K →+* L) (r : R0P.CopyRowExtension K) : R0P.CopyRowExtension L :=
  ⟨fun i=>f (r.producerValues i),fun i=>f (r.producerWeights i),
   fun i=>f (r.consumerValues i),fun i=>f (r.consumerWeights i)⟩
theorem residual (f : K →+* L) (r : R0P.CopyRowExtension K) (h chi : K) :
    f (R0P.copyResidual r h chi)=R0P.copyResidual (row f r) (f h) (f chi) := by
  simp only [R0P.copyResidual,row,Matrix.cons_val_zero,Matrix.cons_val_one,
    Matrix.cons_val_succ,map_sub,map_add,map_mul]
def stepFn {F : Type} [Field F] (s : R0P.CopySelectors F) (p : Fin 14 → F)
    (n : Nat) (v : R0P.Variant) (r : R0P.CopyRowExtension F) (l : R0P.CopyLink) :
    R0P.CopyRowExtension F :=
  let w:=R0P.copyLinkWeight l n v
  let a:=R0P.copyAccumulateEndpoint r.producerValues r.producerWeights l.producer l.tag w p s
  let b:=R0P.copyAccumulateEndpoint r.consumerValues r.consumerWeights l.consumer l.tag w p s
  ⟨a.1,a.2,b.1,b.2⟩
theorem step (f : K →+* L) (s : R0P.CopySelectors K) (p : Fin 14 → K)
    (n : Nat) (v : R0P.Variant) (r : R0P.CopyRowExtension K) (l : R0P.CopyLink) :
    row f (stepFn s p n v r l)=
      stepFn (FJn_CopyMaskMap.selectors f s) (fun i=>f (p i)) n v (row f r) l := by
  have hp:=FJn_CopyEndpointMap.value f r.producerValues r.producerWeights l.producer l.tag
    (R0P.copyLinkWeight l n v) p s
  have hc:=FJn_CopyEndpointMap.value f r.consumerValues r.consumerWeights l.consumer l.tag
    (R0P.copyLinkWeight l n v) p s
  rw [FJn_CopySmallMap.weight] at hp hc
  exact congrArg₂ (fun (a b : (Fin 2 → L) × (Fin 2 → L))=>
    (⟨a.1,a.2,b.1,b.2⟩ : R0P.CopyRowExtension L)) hp hc
#print axioms residual
#print axioms step
end AspisR1.FJn_CopyRowMap
