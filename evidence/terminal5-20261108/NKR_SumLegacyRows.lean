import RPv_FJk_CopyStep
set_option autoImplicit false
noncomputable section
namespace AspisR1.NKR_SumLegacyRows
open FIv_NativeValue (K)

def values (row : R0P.CopyRowExtension K) (g : Fin 4) : K :=
 if h : g.val<2 then row.producerValues ⟨g.val,h⟩
 else row.consumerValues ⟨g.val-2,by have:=g.isLt;omega⟩
def weights (row : R0P.CopyRowExtension K) (g : Fin 4) : K :=
 if h : g.val<2 then row.producerWeights ⟨g.val,h⟩
 else row.consumerWeights ⟨g.val-2,by have:=g.isLt;omega⟩
def group (consumer : Bool) (e : R0P.CopyEndpoint) : Fin 4 :=
 ⟨e.slot.val+(if consumer then 2 else 0),by have:=e.slot.isLt;split <;>omega⟩
def endpoint (link : R0P.CopyLink) (consumer : Bool) : R0P.CopyEndpoint :=
 if consumer then link.consumer else link.producer
def valueTerm (s : R0P.CopySelectors K) (patterns : Fin 14 → K) (link : R0P.CopyLink) (consumer : Bool) : K :=
 let e := endpoint link consumer
 R0P.copySelectorRow s e.row*((link.tag : K)+patterns e.pattern)
def weightTerm (s : R0P.CopySelectors K) (append : Nat) (variant : R0P.Variant)
 (link : R0P.CopyLink) (consumer : Bool) : K :=
 let e := endpoint link consumer
 R0P.copySelectorRow s e.row*R0P.copyLinkWeight link append variant

theorem one_value (s : R0P.CopySelectors K) (patterns : Fin 14 → K) (append : Nat) (variant : R0P.Variant)
 (row : R0P.CopyRowExtension K) (link : R0P.CopyLink) (g : Fin 4) :
 values (FJk_CopyStep.step s patterns append variant row link) g=values row g+
 (if g=group false link.producer then valueTerm s patterns link false else 0)+
 (if g=group true link.consumer then valueTerm s patterns link true else 0) := by
 cases link with
 | mk tag kind level producer consumer =>
  cases producer with
  | mk pr ps pp =>
   cases consumer with
   | mk cr cs cp =>
    fin_cases ps <;> fin_cases cs <;> fin_cases g <;>
     simp [values,FJk_CopyStep.step,R0P.copyAccumulateEndpoint,group,valueTerm,endpoint,Function.update_apply] <;> ring

theorem one_weight (s : R0P.CopySelectors K) (patterns : Fin 14 → K) (append : Nat) (variant : R0P.Variant)
 (row : R0P.CopyRowExtension K) (link : R0P.CopyLink) (g : Fin 4) :
 weights (FJk_CopyStep.step s patterns append variant row link) g=weights row g+
 (if g=group false link.producer then weightTerm s append variant link false else 0)+
 (if g=group true link.consumer then weightTerm s append variant link true else 0) := by
 cases link with
 | mk tag kind level producer consumer =>
  cases producer with
  | mk pr ps pp =>
   cases consumer with
   | mk cr cs cp =>
    fin_cases ps <;> fin_cases cs <;> fin_cases g <;>
     simp [weights,FJk_CopyStep.step,R0P.copyAccumulateEndpoint,group,weightTerm,endpoint,Function.update_apply] <;> ring

/-- Symbolic legacy/cohort rowfold over arbitrary link lists. This makes the
final218join an equality of explicit endpoint sums,not two opaque loops. -/
theorem fold_values (s : R0P.CopySelectors K) (patterns : Fin 14 → K) (append : Nat) (variant : R0P.Variant)
 (row : R0P.CopyRowExtension K) (links : List R0P.CopyLink) (g : Fin 4) :
 values (links.foldl (FJk_CopyStep.step s patterns append variant) row) g=values row g+
 (links.map (fun link=>(if g=group false link.producer then valueTerm s patterns link false else 0)+
 (if g=group true link.consumer then valueTerm s patterns link true else 0))).sum := by
 induction links generalizing row with
 | nil => simp
 | cons link links ih =>
  rw [List.foldl_cons,ih,one_value]
  simp only [List.map_cons,List.sum_cons]
  ring

theorem fold_weights (s : R0P.CopySelectors K) (patterns : Fin 14 → K) (append : Nat) (variant : R0P.Variant)
 (row : R0P.CopyRowExtension K) (links : List R0P.CopyLink) (g : Fin 4) :
 weights (links.foldl (FJk_CopyStep.step s patterns append variant) row) g=weights row g+
 (links.map (fun link=>(if g=group false link.producer then weightTerm s append variant link false else 0)+
 (if g=group true link.consumer then weightTerm s append variant link true else 0))).sum := by
 induction links generalizing row with
 | nil => simp
 | cons link links ih =>
  rw [List.foldl_cons,ih,one_weight]
  simp only [List.map_cons,List.sum_cons]
  ring

#print axioms one_value
#print axioms one_weight
#print axioms fold_values
#print axioms fold_weights
end AspisR1.NKR_SumLegacyRows
end
