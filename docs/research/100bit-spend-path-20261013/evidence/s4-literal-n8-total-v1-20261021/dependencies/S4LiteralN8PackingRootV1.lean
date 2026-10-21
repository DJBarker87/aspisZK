import S4P6ArrayForwardRootV1
import S4FromFnP6InnerN8ConcreteV2
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace AspisR1FastDotsLiteralN8PackingRootV1
abbrev Ops := AspisR1FastDotsCurrent.FourDotsOps
abbrev Limbs := Array Std.U64 8#usize
abbrev Values := Array Std.U32 8#usize
abbrev InnerFn (ops : Ops) :=
  AspisR1FastDotsCurrent.fast_dots.four_dots.closure.closure.Insts.CoreOpsFunctionFnMutTupleUsizeU32 ops

def readReduce (ops : Ops) (limbs : Limbs) (i : Usize) : Result Std.U32 := do
  let word ← Array.index_usize limbs i
  ops.m31ReduceU64 word

private theorem bind_ok_inv {α β : Type} {r : Result α} {f : α → Result β} {x : β}
    (h : Bind.bind r f=.ok x) : ∃ a, r=.ok a ∧ f a=.ok x := by
  cases r with
  | ok a => exact ⟨a,rfl,h⟩
  | fail e => simp [Bind.bind] at h
  | div => simp [Bind.bind] at h

theorem n8_p6_forward_of_read_reduce_total
    (ops : Ops) (limbs : Limbs)
    (hread : ∀ i : Usize, i.val<8 → ∃ value, readReduce ops limbs i=.ok value) :
    ∃ values : Values,
      AspisR1FromFnP6Generated.arrayFromFnP6 8#usize (InnerFn ops) limbs=.ok values := by
  have hcallback : ∀ f i, i.val<(8#usize).val → f=limbs → ∃ value next,
      (InnerFn ops).call_mut f i=.ok (value,next) ∧ True ∧ next=limbs := by
    intro f i hi hf
    subst f
    obtain ⟨value,hr⟩ := hread i (by simpa using hi)
    refine ⟨value,limbs,?_,True.intro,rfl⟩
    change (do
      let word ← Array.index_usize limbs i
      let result ← ops.m31ReduceU64 word
      .ok (result,limbs))=.ok (value,limbs)
    cases hh : Array.index_usize limbs i with
    | fail e => simp only [readReduce,hh,bind_tc_fail] at hr; cases hr
    | div => simp only [readReduce,hh,bind_tc_div] at hr; cases hr
    | ok word =>
      simp only [readReduce,hh,bind_tc_ok] at hr
      simp only [hh,bind_tc_ok,hr]
  obtain ⟨values,hvalues,_⟩ := AspisR1P6ArrayForwardRootV1.array_from_fn_forward
    8#usize (InnerFn ops) (fun f _ => f=limbs) (fun _ => True) limbs
    (by decide) rfl hcallback
  exact ⟨values,hvalues⟩

def literalEight (ops : Ops) (limbs : Limbs) : Result Values := do
  let m0 ← readReduce ops limbs 0#usize
  let m1 ← readReduce ops limbs 1#usize
  let m2 ← readReduce ops limbs 2#usize
  let m3 ← readReduce ops limbs 3#usize
  let m4 ← readReduce ops limbs 4#usize
  let m5 ← readReduce ops limbs 5#usize
  let m6 ← readReduce ops limbs 6#usize
  let m7 ← readReduce ops limbs 7#usize
  .ok (Array.make 8#usize [m0,m1,m2,m3,m4,m5,m6,m7])

/-- Eight successful literal read/reducer calls construct the same retained
P6 N8 array result. No independent array success or canonicality is assumed. -/
theorem literal_eight_success_p6_same_output
    (ops : Ops) (limbs : Limbs) (out : Values)
    (hliteral : literalEight ops limbs=.ok out) :
    AspisR1FromFnP6Generated.arrayFromFnP6 8#usize (InnerFn ops) limbs=.ok out := by
  unfold literalEight at hliteral
  obtain ⟨m0,h0,hliteral⟩ := bind_ok_inv hliteral
  obtain ⟨m1,h1,hliteral⟩ := bind_ok_inv hliteral
  obtain ⟨m2,h2,hliteral⟩ := bind_ok_inv hliteral
  obtain ⟨m3,h3,hliteral⟩ := bind_ok_inv hliteral
  obtain ⟨m4,h4,hliteral⟩ := bind_ok_inv hliteral
  obtain ⟨m5,h5,hliteral⟩ := bind_ok_inv hliteral
  obtain ⟨m6,h6,hliteral⟩ := bind_ok_inv hliteral
  obtain ⟨m7,h7,hliteral⟩ := bind_ok_inv hliteral
  have hout : out=Array.make 8#usize [m0,m1,m2,m3,m4,m5,m6,m7] :=
    (Result.ok.inj hliteral).symm
  have htotal : ∀ i : Usize, i.val<8 → ∃ value, readReduce ops limbs i=.ok value := by
    intro i hi
    rcases (show i.val=0 ∨ i.val=1 ∨ i.val=2 ∨ i.val=3 ∨
      i.val=4 ∨ i.val=5 ∨ i.val=6 ∨ i.val=7 from by omega) with
      hv | hv | hv | hv | hv | hv | hv | hv
    · have he : i=0#usize := UScalar.eq_of_val_eq (by simpa using hv)
      subst i
      exact ⟨m0,h0⟩
    · have he : i=1#usize := UScalar.eq_of_val_eq (by simpa using hv)
      subst i
      exact ⟨m1,h1⟩
    · have he : i=2#usize := UScalar.eq_of_val_eq (by simpa using hv)
      subst i
      exact ⟨m2,h2⟩
    · have he : i=3#usize := UScalar.eq_of_val_eq (by simpa using hv)
      subst i
      exact ⟨m3,h3⟩
    · have he : i=4#usize := UScalar.eq_of_val_eq (by simpa using hv)
      subst i
      exact ⟨m4,h4⟩
    · have he : i=5#usize := UScalar.eq_of_val_eq (by simpa using hv)
      subst i
      exact ⟨m5,h5⟩
    · have he : i=6#usize := UScalar.eq_of_val_eq (by simpa using hv)
      subst i
      exact ⟨m6,h6⟩
    · have he : i=7#usize := UScalar.eq_of_val_eq (by simpa using hv)
      subst i
      exact ⟨m7,h7⟩
  obtain ⟨values,hp6⟩ := n8_p6_forward_of_read_reduce_total ops limbs htotal
  obtain ⟨n0,n1,n2,n3,n4,n5,n6,n7,w0,w1,w2,w3,w4,w5,w6,w7,
    hvals,hi0,hr0,hi1,hr1,hi2,hr2,hi3,hr3,hi4,hr4,hi5,hr5,hi6,hr6,hi7,hr7⟩ :=
    AspisR1FromFnP6Generated.innerArrayP6_success_values_match_fixedV6 ops limbs values hp6
  have hn0 : readReduce ops limbs 0#usize=.ok n0 := by
    simp only [readReduce,hi0,bind_tc_ok,hr0]
  have he0 : n0=m0 := Result.ok.inj (hn0.symm.trans h0)
  have hn1 : readReduce ops limbs 1#usize=.ok n1 := by
    simp only [readReduce,hi1,bind_tc_ok,hr1]
  have he1 : n1=m1 := Result.ok.inj (hn1.symm.trans h1)
  have hn2 : readReduce ops limbs 2#usize=.ok n2 := by
    simp only [readReduce,hi2,bind_tc_ok,hr2]
  have he2 : n2=m2 := Result.ok.inj (hn2.symm.trans h2)
  have hn3 : readReduce ops limbs 3#usize=.ok n3 := by
    simp only [readReduce,hi3,bind_tc_ok,hr3]
  have he3 : n3=m3 := Result.ok.inj (hn3.symm.trans h3)
  have hn4 : readReduce ops limbs 4#usize=.ok n4 := by
    simp only [readReduce,hi4,bind_tc_ok,hr4]
  have he4 : n4=m4 := Result.ok.inj (hn4.symm.trans h4)
  have hn5 : readReduce ops limbs 5#usize=.ok n5 := by
    simp only [readReduce,hi5,bind_tc_ok,hr5]
  have he5 : n5=m5 := Result.ok.inj (hn5.symm.trans h5)
  have hn6 : readReduce ops limbs 6#usize=.ok n6 := by
    simp only [readReduce,hi6,bind_tc_ok,hr6]
  have he6 : n6=m6 := Result.ok.inj (hn6.symm.trans h6)
  have hn7 : readReduce ops limbs 7#usize=.ok n7 := by
    simp only [readReduce,hi7,bind_tc_ok,hr7]
  have he7 : n7=m7 := Result.ok.inj (hn7.symm.trans h7)
  have hbacking : values.val=out.val := by
    rw [hout]
    change values.val=[m0,m1,m2,m3,m4,m5,m6,m7]
    simpa only [he0,he1,he2,he3,he4,he5,he6,he7] using hvals
  have heq : values=out := by
    cases values with
    | mk vl vp =>
      cases out with
      | mk ol op =>
        change vl=ol at hbacking
        subst ol
        rfl
  simpa only [heq] using hp6

#print axioms n8_p6_forward_of_read_reduce_total
#print axioms literal_eight_success_p6_same_output
end AspisR1FastDotsLiteralN8PackingRootV1
