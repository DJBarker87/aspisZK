import NIY_NativeCuts
set_option autoImplicit false
noncomputable section
namespace NIY_WeightFrame
open Aeneas Aeneas.Std NIL_Carriers NIY_NativeCuts

/-- Scalar equality from the actual word value, without enumerating its domain. -/
theorem scalar_ext (x y : U32) (h : x.val=y.val) : x=y := by
 cases x
 cases y
 cases h
 rfl

/-- Four selected native word observations determine the same K value. -/
theorem k_ext (x y : Fresh.K)
 (h : ∀ j : Fin 4,limbK x j.val=limbK y j.val) : x=y := by
 rcases x with ⟨⟨x0,x1⟩,⟨x2,x3⟩⟩
 rcases y with ⟨⟨y0,y1⟩,⟨y2,y3⟩⟩
 have h0 := h ⟨0,by decide⟩
 have h1 := h ⟨1,by decide⟩
 have h2 := h ⟨2,by decide⟩
 have h3 := h ⟨3,by decide⟩
 change x0.val=y0.val at h0
 change x1.val=y1.val at h1
 change x2.val=y2.val at h2
 change x3.val=y3.val at h3
 have e0 := scalar_ext x0 y0 h0
 have e1 := scalar_ext x1 y1 h1
 have e2 := scalar_ext x2 y2 h2
 have e3 := scalar_ext x3 y3 h3
 cases e0;cases e1;cases e2;cases e3
 rfl

def cell (v : alloc.vec.Vec Fresh.K) (size : v.val.length=64) (i : Fin 64) : Fresh.K :=
 v.val[i.val]'(by omega)

/-- Pointwise windows compose on the SAME before/after vectors.
The premise must come from native window certificates on those vectors; this
lemma supplies neither an independent output nor a missing native certificate. -/
theorem payload (before after : alloc.vec.Vec Fresh.K)
 (before_size : before.val.length=64) (after_size : after.val.length=64)
 (windows : ∀ i : Fin 64,∀ j : Fin 4,
   limbK (cell before before_size i) j.val=limbK (cell after after_size i) j.val) :
 before=after := by
 apply Subtype.ext
 apply List.ext_getElem
 · omega
 · intro i hi hj
   apply k_ext
   intro j
   simpa only [cell] using windows ⟨i,by omega⟩ j

/-- Capacity is a native ghost field, not an invented field of the cohort Vec. -/
theorem capacity_prefix (capacity : Nat → Nat) (initial : capacity 0=64)
 (step : ∀ i,i<64 → capacity (i+1)=capacity i) :
 ∀ i,i≤64 → capacity i=64 := by
 intro i
 induction i with
 | zero => intro _;exact initial
 | succ i ih =>
   intro inside
   rw [step i (by omega)]
   exact ih (by omega)

/-- Connect actual reserve, resize and read-weight capacity traces only when
all three observations are on the same producer. These are explicit residual
native observations; this theorem does not assume an output-success fact. -/
theorem capacity_to_final (resize read : Nat → Nat)
 (reserve : resize 0=64)
 (resize_step : ∀ i,i<64 → resize (i+1)=resize i)
 (same_producer : read 0=resize 64)
 (read_step : ∀ i,i<64 → read (i+1)=read i) : read 64=64 := by
 have final_resize := capacity_prefix resize reserve resize_step 64 (by omega)
 have initial_read : read 0=64 := same_producer.trans final_resize
 exact capacity_prefix read initial_read read_step 64 (by omega)

#print axioms scalar_ext
#print axioms k_ext
#print axioms payload
#print axioms capacity_prefix
#print axioms capacity_to_final
end NIY_WeightFrame
