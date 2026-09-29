import AspisV8R19.CircleWeightBridge
import AspisV8R19.NormalizationLoopBridge

namespace AspisR19.CircleChannelsBridge
open AspisV8R17 AspisCircleTensorBinding HighRepairInvariant
open SourceEncodedOpening SourceChordEvaluation NormalizedGCore CircleWeightBridge
noncomputable section
variable {F : Type*} [Field F] [NeZero (2 : F)]

theorem sum_quads (n : Nat) (f : Nat → F) :
    (∑ r ∈ Finset.range (4*n),f r)=
      ∑ i ∈ Finset.range n, (f (4*i)+f (4*i+1)+f (4*i+2)+f (4*i+3)) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [show 4*(n+1)=4*n+1+1+1+1 by omega]
    rw [Finset.sum_range_succ,Finset.sum_range_succ,Finset.sum_range_succ,Finset.sum_range_succ,
      ih,Finset.sum_range_succ]
    ring

theorem flatten_slot (q : Index 32 → F) (i : Fin 32) (k : Fin 4) :
    flatten q (4*i.val+k.val)=q (i,k) := by
  have hi := i.isLt
  have hk := k.isLt
  rw [flatten,dif_pos (show 4*i.val+k.val<128 by omega)]
  congr 1
  apply Prod.ext <;> apply Fin.ext <;> dsimp only <;> omega

def channels (q : Index 32 → F) (z x y : F) : F :=
  NormalizedQuerySection.evaluate (fun i => q (i,0)) z +
    y*NormalizedQuerySection.evaluate (fun i => q (i,1)) z +
    x*NormalizedQuerySection.evaluate (fun i => q (i,2)) z +
    (x*y)*NormalizedQuerySection.evaluate (fun i => q (i,3)) z

theorem serialized_channels (q : Index 32 → F) (x y : F) :
    serialized 1024 (flatten q) x y=channels q (doubledFactor x 1) x y := by
  rw [← serialized_restrict 128 1024 (by decide) _
    (fun r hr _ => by simp [flatten,show ¬r<128 by omega])]
  change (∑ r ∈ Finset.range (4*32),circleWeight x y r*flatten q r)=_
  rw [sum_quads,Finset.sum_range]
  unfold channels NormalizedQuerySection.evaluate
  simp only [Finset.mul_sum,← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  have h0 := circle_four x y i.val (0:Fin 4)
  have h1 := circle_four x y i.val (1:Fin 4)
  have h2 := circle_four x y i.val (2:Fin 4)
  have h3 := circle_four x y i.val (3:Fin 4)
  have f0 := flatten_slot q i (0:Fin 4)
  have f1 := flatten_slot q i (1:Fin 4)
  have f2 := flatten_slot q i (2:Fin 4)
  have f3 := flatten_slot q i (3:Fin 4)
  simp at h0 h1 h2 h3
  simp at f0 f1 f2 f3
  rw [h0,h1,h2,h3,f0,f1,f2,f3]
  ring

theorem input_channels (q : Index 32 → F) (x y : F) :
    inputValue (flatten q) x y=channels q (doubledFactor x 1) x y := by
  have h := serialized_pairs 512 (flatten q) x y
  change serialized 1024 (flatten q) x y=inputValue (flatten q) x y at h
  rw [← h,serialized_channels]

def sourceEvaluate (v : Nat → F) (x y : F) : F :=
  ∑ r ∈ Finset.range 1024, sourceWeight x y r*v r

theorem sourceEvaluate_eq (v : Nat → F) (x y : F) :
    sourceEvaluate v x y=serialized 1024 v x y := by
  unfold sourceEvaluate serialized
  apply Finset.sum_congr rfl
  intro r hr
  rw [sourceWeight_eq x y r (Finset.mem_range.mp hr)]

theorem sourceEvaluate_channels (q : Index 32 → F) (x y : F) :
    sourceEvaluate (flatten q) x y=channels q (doubledFactor x 1) x y := by
  rw [sourceEvaluate_eq,serialized_channels]

theorem source_quotient_root (t : Fin 22 → F) (ht : Function.Injective t)
    (alpha : F) (d : Fin 32) (s : Fin 4) (j : Fin 22) (x y : F)
    (root : doubledFactor x 1=t j) :
    sourceEvaluate (flatten (NormalizedQuotient.quotient t ht alpha d s)) x y=0 := by
  rw [sourceEvaluate_channels,root]
  simp only [channels,NormalizedQuotient.quotient_root,mul_zero,add_zero]

#print axioms sum_quads
#print axioms flatten_slot
#print axioms serialized_channels
#print axioms input_channels
#print axioms sourceEvaluate_eq
#print axioms sourceEvaluate_channels
#print axioms source_quotient_root
end
end AspisR19.CircleChannelsBridge
