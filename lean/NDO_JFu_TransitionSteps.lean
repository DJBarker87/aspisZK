import NDO_JFu_TransitionSecond
set_option autoImplicit false
noncomputable section
namespace AspisR1.JFu_TransitionSteps
open Aeneas Aeneas.Std Result WP FIq_Native
open pool_v1.pair_forest_semantic_terminal
def r00 : core.ops.range.Range Usize := ⟨0#usize,20#usize⟩
def r01 : core.ops.range.Range Usize := ⟨1#usize,20#usize⟩
def r02 : core.ops.range.Range Usize := ⟨2#usize,20#usize⟩
def r03 : core.ops.range.Range Usize := ⟨3#usize,20#usize⟩
def r04 : core.ops.range.Range Usize := ⟨4#usize,20#usize⟩
def r05 : core.ops.range.Range Usize := ⟨5#usize,20#usize⟩
def r06 : core.ops.range.Range Usize := ⟨6#usize,20#usize⟩
def r07 : core.ops.range.Range Usize := ⟨7#usize,20#usize⟩
def r08 : core.ops.range.Range Usize := ⟨8#usize,20#usize⟩
def r09 : core.ops.range.Range Usize := ⟨9#usize,20#usize⟩
def r10 : core.ops.range.Range Usize := ⟨10#usize,20#usize⟩
def r11 : core.ops.range.Range Usize := ⟨11#usize,20#usize⟩
def r12 : core.ops.range.Range Usize := ⟨12#usize,20#usize⟩
def r13 : core.ops.range.Range Usize := ⟨13#usize,20#usize⟩
def r14 : core.ops.range.Range Usize := ⟨14#usize,20#usize⟩
def r15 : core.ops.range.Range Usize := ⟨15#usize,20#usize⟩
def r16 : core.ops.range.Range Usize := ⟨16#usize,20#usize⟩
def r17 : core.ops.range.Range Usize := ⟨17#usize,20#usize⟩
def r18 : core.ops.range.Range Usize := ⟨18#usize,20#usize⟩
def r19 : core.ops.range.Range Usize := ⟨19#usize,20#usize⟩
def r20 : core.ops.range.Range Usize := ⟨20#usize,20#usize⟩
theorem next00 : Aeneas.Std.core.iter.range.IteratorRange.next Aeneas.Std.core.iter.range.StepUsize r00=
    ok (some 0#usize,r01) := by
  obtain ⟨r,call,start,finish,_⟩ := ExtractedMaskForwardRange.next_step r00 (by change 0<20;omega)
  have sameStart : r.start=1#usize := UScalar.eq_of_val_eq (by
    change r.start.val=1;change r.start.val=0+1 at start;omega)
  have same : r=r01 := by cases r;simp_all [r00,r01]
  simpa only [same,r00] using call
#print axioms next00
theorem next01 : Aeneas.Std.core.iter.range.IteratorRange.next Aeneas.Std.core.iter.range.StepUsize r01=
    ok (some 1#usize,r02) := by
  obtain ⟨r,call,start,finish,_⟩ := ExtractedMaskForwardRange.next_step r01 (by change 1<20;omega)
  have sameStart : r.start=2#usize := UScalar.eq_of_val_eq (by
    change r.start.val=2;change r.start.val=1+1 at start;omega)
  have same : r=r02 := by cases r;simp_all [r01,r02]
  simpa only [same,r01] using call
#print axioms next01
theorem next02 : Aeneas.Std.core.iter.range.IteratorRange.next Aeneas.Std.core.iter.range.StepUsize r02=
    ok (some 2#usize,r03) := by
  obtain ⟨r,call,start,finish,_⟩ := ExtractedMaskForwardRange.next_step r02 (by change 2<20;omega)
  have sameStart : r.start=3#usize := UScalar.eq_of_val_eq (by
    change r.start.val=3;change r.start.val=2+1 at start;omega)
  have same : r=r03 := by cases r;simp_all [r02,r03]
  simpa only [same,r02] using call
#print axioms next02
theorem next03 : Aeneas.Std.core.iter.range.IteratorRange.next Aeneas.Std.core.iter.range.StepUsize r03=
    ok (some 3#usize,r04) := by
  obtain ⟨r,call,start,finish,_⟩ := ExtractedMaskForwardRange.next_step r03 (by change 3<20;omega)
  have sameStart : r.start=4#usize := UScalar.eq_of_val_eq (by
    change r.start.val=4;change r.start.val=3+1 at start;omega)
  have same : r=r04 := by cases r;simp_all [r03,r04]
  simpa only [same,r03] using call
#print axioms next03
theorem next04 : Aeneas.Std.core.iter.range.IteratorRange.next Aeneas.Std.core.iter.range.StepUsize r04=
    ok (some 4#usize,r05) := by
  obtain ⟨r,call,start,finish,_⟩ := ExtractedMaskForwardRange.next_step r04 (by change 4<20;omega)
  have sameStart : r.start=5#usize := UScalar.eq_of_val_eq (by
    change r.start.val=5;change r.start.val=4+1 at start;omega)
  have same : r=r05 := by cases r;simp_all [r04,r05]
  simpa only [same,r04] using call
#print axioms next04
theorem next05 : Aeneas.Std.core.iter.range.IteratorRange.next Aeneas.Std.core.iter.range.StepUsize r05=
    ok (some 5#usize,r06) := by
  obtain ⟨r,call,start,finish,_⟩ := ExtractedMaskForwardRange.next_step r05 (by change 5<20;omega)
  have sameStart : r.start=6#usize := UScalar.eq_of_val_eq (by
    change r.start.val=6;change r.start.val=5+1 at start;omega)
  have same : r=r06 := by cases r;simp_all [r05,r06]
  simpa only [same,r05] using call
#print axioms next05
theorem next06 : Aeneas.Std.core.iter.range.IteratorRange.next Aeneas.Std.core.iter.range.StepUsize r06=
    ok (some 6#usize,r07) := by
  obtain ⟨r,call,start,finish,_⟩ := ExtractedMaskForwardRange.next_step r06 (by change 6<20;omega)
  have sameStart : r.start=7#usize := UScalar.eq_of_val_eq (by
    change r.start.val=7;change r.start.val=6+1 at start;omega)
  have same : r=r07 := by cases r;simp_all [r06,r07]
  simpa only [same,r06] using call
#print axioms next06
theorem next07 : Aeneas.Std.core.iter.range.IteratorRange.next Aeneas.Std.core.iter.range.StepUsize r07=
    ok (some 7#usize,r08) := by
  obtain ⟨r,call,start,finish,_⟩ := ExtractedMaskForwardRange.next_step r07 (by change 7<20;omega)
  have sameStart : r.start=8#usize := UScalar.eq_of_val_eq (by
    change r.start.val=8;change r.start.val=7+1 at start;omega)
  have same : r=r08 := by cases r;simp_all [r07,r08]
  simpa only [same,r07] using call
#print axioms next07
theorem next08 : Aeneas.Std.core.iter.range.IteratorRange.next Aeneas.Std.core.iter.range.StepUsize r08=
    ok (some 8#usize,r09) := by
  obtain ⟨r,call,start,finish,_⟩ := ExtractedMaskForwardRange.next_step r08 (by change 8<20;omega)
  have sameStart : r.start=9#usize := UScalar.eq_of_val_eq (by
    change r.start.val=9;change r.start.val=8+1 at start;omega)
  have same : r=r09 := by cases r;simp_all [r08,r09]
  simpa only [same,r08] using call
#print axioms next08
theorem next09 : Aeneas.Std.core.iter.range.IteratorRange.next Aeneas.Std.core.iter.range.StepUsize r09=
    ok (some 9#usize,r10) := by
  obtain ⟨r,call,start,finish,_⟩ := ExtractedMaskForwardRange.next_step r09 (by change 9<20;omega)
  have sameStart : r.start=10#usize := UScalar.eq_of_val_eq (by
    change r.start.val=10;change r.start.val=9+1 at start;omega)
  have same : r=r10 := by cases r;simp_all [r09,r10]
  simpa only [same,r09] using call
#print axioms next09
theorem next10 : Aeneas.Std.core.iter.range.IteratorRange.next Aeneas.Std.core.iter.range.StepUsize r10=
    ok (some 10#usize,r11) := by
  obtain ⟨r,call,start,finish,_⟩ := ExtractedMaskForwardRange.next_step r10 (by change 10<20;omega)
  have sameStart : r.start=11#usize := UScalar.eq_of_val_eq (by
    change r.start.val=11;change r.start.val=10+1 at start;omega)
  have same : r=r11 := by cases r;simp_all [r10,r11]
  simpa only [same,r10] using call
#print axioms next10
theorem next11 : Aeneas.Std.core.iter.range.IteratorRange.next Aeneas.Std.core.iter.range.StepUsize r11=
    ok (some 11#usize,r12) := by
  obtain ⟨r,call,start,finish,_⟩ := ExtractedMaskForwardRange.next_step r11 (by change 11<20;omega)
  have sameStart : r.start=12#usize := UScalar.eq_of_val_eq (by
    change r.start.val=12;change r.start.val=11+1 at start;omega)
  have same : r=r12 := by cases r;simp_all [r11,r12]
  simpa only [same,r11] using call
#print axioms next11
theorem next12 : Aeneas.Std.core.iter.range.IteratorRange.next Aeneas.Std.core.iter.range.StepUsize r12=
    ok (some 12#usize,r13) := by
  obtain ⟨r,call,start,finish,_⟩ := ExtractedMaskForwardRange.next_step r12 (by change 12<20;omega)
  have sameStart : r.start=13#usize := UScalar.eq_of_val_eq (by
    change r.start.val=13;change r.start.val=12+1 at start;omega)
  have same : r=r13 := by cases r;simp_all [r12,r13]
  simpa only [same,r12] using call
#print axioms next12
theorem next13 : Aeneas.Std.core.iter.range.IteratorRange.next Aeneas.Std.core.iter.range.StepUsize r13=
    ok (some 13#usize,r14) := by
  obtain ⟨r,call,start,finish,_⟩ := ExtractedMaskForwardRange.next_step r13 (by change 13<20;omega)
  have sameStart : r.start=14#usize := UScalar.eq_of_val_eq (by
    change r.start.val=14;change r.start.val=13+1 at start;omega)
  have same : r=r14 := by cases r;simp_all [r13,r14]
  simpa only [same,r13] using call
#print axioms next13
theorem next14 : Aeneas.Std.core.iter.range.IteratorRange.next Aeneas.Std.core.iter.range.StepUsize r14=
    ok (some 14#usize,r15) := by
  obtain ⟨r,call,start,finish,_⟩ := ExtractedMaskForwardRange.next_step r14 (by change 14<20;omega)
  have sameStart : r.start=15#usize := UScalar.eq_of_val_eq (by
    change r.start.val=15;change r.start.val=14+1 at start;omega)
  have same : r=r15 := by cases r;simp_all [r14,r15]
  simpa only [same,r14] using call
#print axioms next14
theorem next15 : Aeneas.Std.core.iter.range.IteratorRange.next Aeneas.Std.core.iter.range.StepUsize r15=
    ok (some 15#usize,r16) := by
  obtain ⟨r,call,start,finish,_⟩ := ExtractedMaskForwardRange.next_step r15 (by change 15<20;omega)
  have sameStart : r.start=16#usize := UScalar.eq_of_val_eq (by
    change r.start.val=16;change r.start.val=15+1 at start;omega)
  have same : r=r16 := by cases r;simp_all [r15,r16]
  simpa only [same,r15] using call
#print axioms next15
theorem next16 : Aeneas.Std.core.iter.range.IteratorRange.next Aeneas.Std.core.iter.range.StepUsize r16=
    ok (some 16#usize,r17) := by
  obtain ⟨r,call,start,finish,_⟩ := ExtractedMaskForwardRange.next_step r16 (by change 16<20;omega)
  have sameStart : r.start=17#usize := UScalar.eq_of_val_eq (by
    change r.start.val=17;change r.start.val=16+1 at start;omega)
  have same : r=r17 := by cases r;simp_all [r16,r17]
  simpa only [same,r16] using call
#print axioms next16
theorem next17 : Aeneas.Std.core.iter.range.IteratorRange.next Aeneas.Std.core.iter.range.StepUsize r17=
    ok (some 17#usize,r18) := by
  obtain ⟨r,call,start,finish,_⟩ := ExtractedMaskForwardRange.next_step r17 (by change 17<20;omega)
  have sameStart : r.start=18#usize := UScalar.eq_of_val_eq (by
    change r.start.val=18;change r.start.val=17+1 at start;omega)
  have same : r=r18 := by cases r;simp_all [r17,r18]
  simpa only [same,r17] using call
#print axioms next17
theorem next18 : Aeneas.Std.core.iter.range.IteratorRange.next Aeneas.Std.core.iter.range.StepUsize r18=
    ok (some 18#usize,r19) := by
  obtain ⟨r,call,start,finish,_⟩ := ExtractedMaskForwardRange.next_step r18 (by change 18<20;omega)
  have sameStart : r.start=19#usize := UScalar.eq_of_val_eq (by
    change r.start.val=19;change r.start.val=18+1 at start;omega)
  have same : r=r19 := by cases r;simp_all [r18,r19]
  simpa only [same,r18] using call
#print axioms next18
theorem next19 : Aeneas.Std.core.iter.range.IteratorRange.next Aeneas.Std.core.iter.range.StepUsize r19=
    ok (some 19#usize,r20) := by
  obtain ⟨r,call,start,finish,_⟩ := ExtractedMaskForwardRange.next_step r19 (by change 19<20;omega)
  have sameStart : r.start=20#usize := UScalar.eq_of_val_eq (by
    change r.start.val=20;change r.start.val=19+1 at start;omega)
  have same : r=r20 := by cases r;simp_all [r19,r20]
  simpa only [same,r19] using call
#print axioms next19
theorem shifted03 : (13#u64 >>> 3#usize : Result U64)=ok 1#u64 := by
  have spec : (13#u64 >>> 3#usize : Result U64) ⦃ out => out.val=1 ⦄ := by
    step* <;> scalar_tac
  obtain ⟨out,call,value⟩ := WP.spec_imp_exists spec
  have same : out=1#u64 := UScalar.eq_of_val_eq value
  exact same ▸ call
#print axioms shifted03
theorem shifted04 : (13#u64 >>> 4#usize : Result U64)=ok 0#u64 := by
  have spec : (13#u64 >>> 4#usize : Result U64) ⦃ out => out.val=0 ⦄ := by
    step* <;> scalar_tac
  obtain ⟨out,call,value⟩ := WP.spec_imp_exists spec
  have same : out=0#u64 := UScalar.eq_of_val_eq value
  exact same ▸ call
#print axioms shifted04
theorem shifted05 : (13#u64 >>> 5#usize : Result U64)=ok 0#u64 := by
  have spec : (13#u64 >>> 5#usize : Result U64) ⦃ out => out.val=0 ⦄ := by
    step* <;> scalar_tac
  obtain ⟨out,call,value⟩ := WP.spec_imp_exists spec
  have same : out=0#u64 := UScalar.eq_of_val_eq value
  exact same ▸ call
#print axioms shifted05
theorem shifted06 : (13#u64 >>> 6#usize : Result U64)=ok 0#u64 := by
  have spec : (13#u64 >>> 6#usize : Result U64) ⦃ out => out.val=0 ⦄ := by
    step* <;> scalar_tac
  obtain ⟨out,call,value⟩ := WP.spec_imp_exists spec
  have same : out=0#u64 := UScalar.eq_of_val_eq value
  exact same ▸ call
#print axioms shifted06
theorem shifted07 : (13#u64 >>> 7#usize : Result U64)=ok 0#u64 := by
  have spec : (13#u64 >>> 7#usize : Result U64) ⦃ out => out.val=0 ⦄ := by
    step* <;> scalar_tac
  obtain ⟨out,call,value⟩ := WP.spec_imp_exists spec
  have same : out=0#u64 := UScalar.eq_of_val_eq value
  exact same ▸ call
#print axioms shifted07
theorem shifted08 : (13#u64 >>> 8#usize : Result U64)=ok 0#u64 := by
  have spec : (13#u64 >>> 8#usize : Result U64) ⦃ out => out.val=0 ⦄ := by
    step* <;> scalar_tac
  obtain ⟨out,call,value⟩ := WP.spec_imp_exists spec
  have same : out=0#u64 := UScalar.eq_of_val_eq value
  exact same ▸ call
#print axioms shifted08
theorem shifted09 : (13#u64 >>> 9#usize : Result U64)=ok 0#u64 := by
  have spec : (13#u64 >>> 9#usize : Result U64) ⦃ out => out.val=0 ⦄ := by
    step* <;> scalar_tac
  obtain ⟨out,call,value⟩ := WP.spec_imp_exists spec
  have same : out=0#u64 := UScalar.eq_of_val_eq value
  exact same ▸ call
#print axioms shifted09
theorem shifted10 : (13#u64 >>> 10#usize : Result U64)=ok 0#u64 := by
  have spec : (13#u64 >>> 10#usize : Result U64) ⦃ out => out.val=0 ⦄ := by
    step* <;> scalar_tac
  obtain ⟨out,call,value⟩ := WP.spec_imp_exists spec
  have same : out=0#u64 := UScalar.eq_of_val_eq value
  exact same ▸ call
#print axioms shifted10
theorem shifted11 : (13#u64 >>> 11#usize : Result U64)=ok 0#u64 := by
  have spec : (13#u64 >>> 11#usize : Result U64) ⦃ out => out.val=0 ⦄ := by
    step* <;> scalar_tac
  obtain ⟨out,call,value⟩ := WP.spec_imp_exists spec
  have same : out=0#u64 := UScalar.eq_of_val_eq value
  exact same ▸ call
#print axioms shifted11
theorem shifted12 : (13#u64 >>> 12#usize : Result U64)=ok 0#u64 := by
  have spec : (13#u64 >>> 12#usize : Result U64) ⦃ out => out.val=0 ⦄ := by
    step* <;> scalar_tac
  obtain ⟨out,call,value⟩ := WP.spec_imp_exists spec
  have same : out=0#u64 := UScalar.eq_of_val_eq value
  exact same ▸ call
#print axioms shifted12
theorem shifted13 : (13#u64 >>> 13#usize : Result U64)=ok 0#u64 := by
  have spec : (13#u64 >>> 13#usize : Result U64) ⦃ out => out.val=0 ⦄ := by
    step* <;> scalar_tac
  obtain ⟨out,call,value⟩ := WP.spec_imp_exists spec
  have same : out=0#u64 := UScalar.eq_of_val_eq value
  exact same ▸ call
#print axioms shifted13
theorem shifted14 : (13#u64 >>> 14#usize : Result U64)=ok 0#u64 := by
  have spec : (13#u64 >>> 14#usize : Result U64) ⦃ out => out.val=0 ⦄ := by
    step* <;> scalar_tac
  obtain ⟨out,call,value⟩ := WP.spec_imp_exists spec
  have same : out=0#u64 := UScalar.eq_of_val_eq value
  exact same ▸ call
#print axioms shifted14
theorem shifted15 : (13#u64 >>> 15#usize : Result U64)=ok 0#u64 := by
  have spec : (13#u64 >>> 15#usize : Result U64) ⦃ out => out.val=0 ⦄ := by
    step* <;> scalar_tac
  obtain ⟨out,call,value⟩ := WP.spec_imp_exists spec
  have same : out=0#u64 := UScalar.eq_of_val_eq value
  exact same ▸ call
#print axioms shifted15
theorem shifted16 : (13#u64 >>> 16#usize : Result U64)=ok 0#u64 := by
  have spec : (13#u64 >>> 16#usize : Result U64) ⦃ out => out.val=0 ⦄ := by
    step* <;> scalar_tac
  obtain ⟨out,call,value⟩ := WP.spec_imp_exists spec
  have same : out=0#u64 := UScalar.eq_of_val_eq value
  exact same ▸ call
#print axioms shifted16
theorem shifted17 : (13#u64 >>> 17#usize : Result U64)=ok 0#u64 := by
  have spec : (13#u64 >>> 17#usize : Result U64) ⦃ out => out.val=0 ⦄ := by
    step* <;> scalar_tac
  obtain ⟨out,call,value⟩ := WP.spec_imp_exists spec
  have same : out=0#u64 := UScalar.eq_of_val_eq value
  exact same ▸ call
#print axioms shifted17
theorem shifted18 : (13#u64 >>> 18#usize : Result U64)=ok 0#u64 := by
  have spec : (13#u64 >>> 18#usize : Result U64) ⦃ out => out.val=0 ⦄ := by
    step* <;> scalar_tac
  obtain ⟨out,call,value⟩ := WP.spec_imp_exists spec
  have same : out=0#u64 := UScalar.eq_of_val_eq value
  exact same ▸ call
#print axioms shifted18
theorem shifted19 : (13#u64 >>> 19#usize : Result U64)=ok 0#u64 := by
  have spec : (13#u64 >>> 19#usize : Result U64) ⦃ out => out.val=0 ⦄ := by
    step* <;> scalar_tac
  obtain ⟨out,call,value⟩ := WP.spec_imp_exists spec
  have same : out=0#u64 := UScalar.eq_of_val_eq value
  exact same ▸ call
#print axioms shifted19
theorem step00 : validate_transition_loop JFu_PublicSemantic.value r00 1#usize=
    validate_transition_loop JFu_PublicSemantic.value r01 1#usize := by
  exact JFu_TransitionFirst.step
#print axioms step00
theorem step01 : validate_transition_loop JFu_PublicSemantic.value r01 1#usize=
    validate_transition_loop JFu_PublicSemantic.value r02 1#usize := by
  rw [validate_transition_loop,next01,bind_tc_ok]
  simp only [Aeneas.Std.uncurry,if_pos (by rfl : 1#usize=1#usize),
    if_pos (by scalar_tac : 1#usize<20#usize),ite_true]
#print axioms step01
theorem step02 : validate_transition_loop JFu_PublicSemantic.value r02 1#usize=
    validate_transition_loop JFu_PublicSemantic.value r03 1#usize := by
  exact JFu_TransitionSecond.step
#print axioms step02
theorem step03 : validate_transition_loop JFu_PublicSemantic.value r03 1#usize=
    validate_transition_loop JFu_PublicSemantic.value r04 1#usize := by
  rw [validate_transition_loop,next03,bind_tc_ok]
  simp only [Aeneas.Std.uncurry,if_neg (by scalar_tac : ¬(3#usize=1#usize)),
    if_neg (by scalar_tac : ¬(3#usize<1#usize))]
  have shifted : JFu_PublicSemantic.value.transition.live_snapshot.next_pair_index >>> 3#usize=ok 1#u64 := shifted03
  rw [shifted,bind_tc_ok]
  have bit : lift (1#u64 &&& 1#u64)=ok 1#u64 := rfl
  rw [bit,bind_tc_ok]
  simp only [if_neg (by scalar_tac : ¬(1#u64=0#u64)),bind_tc_ok,Aeneas.Std.uncurry]
  rfl
#print axioms step03
theorem step04 : validate_transition_loop JFu_PublicSemantic.value r04 1#usize=
    validate_transition_loop JFu_PublicSemantic.value r05 1#usize := by
  rw [validate_transition_loop,next04,bind_tc_ok]
  simp only [Aeneas.Std.uncurry,if_neg (by scalar_tac : ¬(4#usize=1#usize)),
    if_neg (by scalar_tac : ¬(4#usize<1#usize))]
  have shifted : JFu_PublicSemantic.value.transition.live_snapshot.next_pair_index >>> 4#usize=ok 0#u64 := shifted04
  rw [shifted,bind_tc_ok]
  have bit : lift (0#u64 &&& 1#u64)=ok 0#u64 := rfl
  rw [bit,bind_tc_ok]
  simp only [if_pos (by rfl : 0#u64=0#u64),bind_tc_ok,Aeneas.Std.uncurry]
  unfold empty_root pool_v1.pair_forest_semantic_terminal.constants.POOL_V1_PAIR_EMPTY_ROOTS_V1
  rfl
#print axioms step04
theorem step05 : validate_transition_loop JFu_PublicSemantic.value r05 1#usize=
    validate_transition_loop JFu_PublicSemantic.value r06 1#usize := by
  rw [validate_transition_loop,next05,bind_tc_ok]
  simp only [Aeneas.Std.uncurry,if_neg (by scalar_tac : ¬(5#usize=1#usize)),
    if_neg (by scalar_tac : ¬(5#usize<1#usize))]
  have shifted : JFu_PublicSemantic.value.transition.live_snapshot.next_pair_index >>> 5#usize=ok 0#u64 := shifted05
  rw [shifted,bind_tc_ok]
  have bit : lift (0#u64 &&& 1#u64)=ok 0#u64 := rfl
  rw [bit,bind_tc_ok]
  simp only [if_pos (by rfl : 0#u64=0#u64),bind_tc_ok,Aeneas.Std.uncurry]
  unfold empty_root pool_v1.pair_forest_semantic_terminal.constants.POOL_V1_PAIR_EMPTY_ROOTS_V1
  rfl
#print axioms step05
theorem step06 : validate_transition_loop JFu_PublicSemantic.value r06 1#usize=
    validate_transition_loop JFu_PublicSemantic.value r07 1#usize := by
  rw [validate_transition_loop,next06,bind_tc_ok]
  simp only [Aeneas.Std.uncurry,if_neg (by scalar_tac : ¬(6#usize=1#usize)),
    if_neg (by scalar_tac : ¬(6#usize<1#usize))]
  have shifted : JFu_PublicSemantic.value.transition.live_snapshot.next_pair_index >>> 6#usize=ok 0#u64 := shifted06
  rw [shifted,bind_tc_ok]
  have bit : lift (0#u64 &&& 1#u64)=ok 0#u64 := rfl
  rw [bit,bind_tc_ok]
  simp only [if_pos (by rfl : 0#u64=0#u64),bind_tc_ok,Aeneas.Std.uncurry]
  unfold empty_root pool_v1.pair_forest_semantic_terminal.constants.POOL_V1_PAIR_EMPTY_ROOTS_V1
  rfl
#print axioms step06
theorem step07 : validate_transition_loop JFu_PublicSemantic.value r07 1#usize=
    validate_transition_loop JFu_PublicSemantic.value r08 1#usize := by
  rw [validate_transition_loop,next07,bind_tc_ok]
  simp only [Aeneas.Std.uncurry,if_neg (by scalar_tac : ¬(7#usize=1#usize)),
    if_neg (by scalar_tac : ¬(7#usize<1#usize))]
  have shifted : JFu_PublicSemantic.value.transition.live_snapshot.next_pair_index >>> 7#usize=ok 0#u64 := shifted07
  rw [shifted,bind_tc_ok]
  have bit : lift (0#u64 &&& 1#u64)=ok 0#u64 := rfl
  rw [bit,bind_tc_ok]
  simp only [if_pos (by rfl : 0#u64=0#u64),bind_tc_ok,Aeneas.Std.uncurry]
  unfold empty_root pool_v1.pair_forest_semantic_terminal.constants.POOL_V1_PAIR_EMPTY_ROOTS_V1
  rfl
#print axioms step07
theorem step08 : validate_transition_loop JFu_PublicSemantic.value r08 1#usize=
    validate_transition_loop JFu_PublicSemantic.value r09 1#usize := by
  rw [validate_transition_loop,next08,bind_tc_ok]
  simp only [Aeneas.Std.uncurry,if_neg (by scalar_tac : ¬(8#usize=1#usize)),
    if_neg (by scalar_tac : ¬(8#usize<1#usize))]
  have shifted : JFu_PublicSemantic.value.transition.live_snapshot.next_pair_index >>> 8#usize=ok 0#u64 := shifted08
  rw [shifted,bind_tc_ok]
  have bit : lift (0#u64 &&& 1#u64)=ok 0#u64 := rfl
  rw [bit,bind_tc_ok]
  simp only [if_pos (by rfl : 0#u64=0#u64),bind_tc_ok,Aeneas.Std.uncurry]
  unfold empty_root pool_v1.pair_forest_semantic_terminal.constants.POOL_V1_PAIR_EMPTY_ROOTS_V1
  rfl
#print axioms step08
theorem step09 : validate_transition_loop JFu_PublicSemantic.value r09 1#usize=
    validate_transition_loop JFu_PublicSemantic.value r10 1#usize := by
  rw [validate_transition_loop,next09,bind_tc_ok]
  simp only [Aeneas.Std.uncurry,if_neg (by scalar_tac : ¬(9#usize=1#usize)),
    if_neg (by scalar_tac : ¬(9#usize<1#usize))]
  have shifted : JFu_PublicSemantic.value.transition.live_snapshot.next_pair_index >>> 9#usize=ok 0#u64 := shifted09
  rw [shifted,bind_tc_ok]
  have bit : lift (0#u64 &&& 1#u64)=ok 0#u64 := rfl
  rw [bit,bind_tc_ok]
  simp only [if_pos (by rfl : 0#u64=0#u64),bind_tc_ok,Aeneas.Std.uncurry]
  unfold empty_root pool_v1.pair_forest_semantic_terminal.constants.POOL_V1_PAIR_EMPTY_ROOTS_V1
  rfl
#print axioms step09
theorem step10 : validate_transition_loop JFu_PublicSemantic.value r10 1#usize=
    validate_transition_loop JFu_PublicSemantic.value r11 1#usize := by
  rw [validate_transition_loop,next10,bind_tc_ok]
  simp only [Aeneas.Std.uncurry,if_neg (by scalar_tac : ¬(10#usize=1#usize)),
    if_neg (by scalar_tac : ¬(10#usize<1#usize))]
  have shifted : JFu_PublicSemantic.value.transition.live_snapshot.next_pair_index >>> 10#usize=ok 0#u64 := shifted10
  rw [shifted,bind_tc_ok]
  have bit : lift (0#u64 &&& 1#u64)=ok 0#u64 := rfl
  rw [bit,bind_tc_ok]
  simp only [if_pos (by rfl : 0#u64=0#u64),bind_tc_ok,Aeneas.Std.uncurry]
  unfold empty_root pool_v1.pair_forest_semantic_terminal.constants.POOL_V1_PAIR_EMPTY_ROOTS_V1
  rfl
#print axioms step10
theorem step11 : validate_transition_loop JFu_PublicSemantic.value r11 1#usize=
    validate_transition_loop JFu_PublicSemantic.value r12 1#usize := by
  rw [validate_transition_loop,next11,bind_tc_ok]
  simp only [Aeneas.Std.uncurry,if_neg (by scalar_tac : ¬(11#usize=1#usize)),
    if_neg (by scalar_tac : ¬(11#usize<1#usize))]
  have shifted : JFu_PublicSemantic.value.transition.live_snapshot.next_pair_index >>> 11#usize=ok 0#u64 := shifted11
  rw [shifted,bind_tc_ok]
  have bit : lift (0#u64 &&& 1#u64)=ok 0#u64 := rfl
  rw [bit,bind_tc_ok]
  simp only [if_pos (by rfl : 0#u64=0#u64),bind_tc_ok,Aeneas.Std.uncurry]
  unfold empty_root pool_v1.pair_forest_semantic_terminal.constants.POOL_V1_PAIR_EMPTY_ROOTS_V1
  rfl
#print axioms step11
theorem step12 : validate_transition_loop JFu_PublicSemantic.value r12 1#usize=
    validate_transition_loop JFu_PublicSemantic.value r13 1#usize := by
  rw [validate_transition_loop,next12,bind_tc_ok]
  simp only [Aeneas.Std.uncurry,if_neg (by scalar_tac : ¬(12#usize=1#usize)),
    if_neg (by scalar_tac : ¬(12#usize<1#usize))]
  have shifted : JFu_PublicSemantic.value.transition.live_snapshot.next_pair_index >>> 12#usize=ok 0#u64 := shifted12
  rw [shifted,bind_tc_ok]
  have bit : lift (0#u64 &&& 1#u64)=ok 0#u64 := rfl
  rw [bit,bind_tc_ok]
  simp only [if_pos (by rfl : 0#u64=0#u64),bind_tc_ok,Aeneas.Std.uncurry]
  unfold empty_root pool_v1.pair_forest_semantic_terminal.constants.POOL_V1_PAIR_EMPTY_ROOTS_V1
  rfl
#print axioms step12
theorem step13 : validate_transition_loop JFu_PublicSemantic.value r13 1#usize=
    validate_transition_loop JFu_PublicSemantic.value r14 1#usize := by
  rw [validate_transition_loop,next13,bind_tc_ok]
  simp only [Aeneas.Std.uncurry,if_neg (by scalar_tac : ¬(13#usize=1#usize)),
    if_neg (by scalar_tac : ¬(13#usize<1#usize))]
  have shifted : JFu_PublicSemantic.value.transition.live_snapshot.next_pair_index >>> 13#usize=ok 0#u64 := shifted13
  rw [shifted,bind_tc_ok]
  have bit : lift (0#u64 &&& 1#u64)=ok 0#u64 := rfl
  rw [bit,bind_tc_ok]
  simp only [if_pos (by rfl : 0#u64=0#u64),bind_tc_ok,Aeneas.Std.uncurry]
  unfold empty_root pool_v1.pair_forest_semantic_terminal.constants.POOL_V1_PAIR_EMPTY_ROOTS_V1
  rfl
#print axioms step13
theorem step14 : validate_transition_loop JFu_PublicSemantic.value r14 1#usize=
    validate_transition_loop JFu_PublicSemantic.value r15 1#usize := by
  rw [validate_transition_loop,next14,bind_tc_ok]
  simp only [Aeneas.Std.uncurry,if_neg (by scalar_tac : ¬(14#usize=1#usize)),
    if_neg (by scalar_tac : ¬(14#usize<1#usize))]
  have shifted : JFu_PublicSemantic.value.transition.live_snapshot.next_pair_index >>> 14#usize=ok 0#u64 := shifted14
  rw [shifted,bind_tc_ok]
  have bit : lift (0#u64 &&& 1#u64)=ok 0#u64 := rfl
  rw [bit,bind_tc_ok]
  simp only [if_pos (by rfl : 0#u64=0#u64),bind_tc_ok,Aeneas.Std.uncurry]
  unfold empty_root pool_v1.pair_forest_semantic_terminal.constants.POOL_V1_PAIR_EMPTY_ROOTS_V1
  rfl
#print axioms step14
theorem step15 : validate_transition_loop JFu_PublicSemantic.value r15 1#usize=
    validate_transition_loop JFu_PublicSemantic.value r16 1#usize := by
  rw [validate_transition_loop,next15,bind_tc_ok]
  simp only [Aeneas.Std.uncurry,if_neg (by scalar_tac : ¬(15#usize=1#usize)),
    if_neg (by scalar_tac : ¬(15#usize<1#usize))]
  have shifted : JFu_PublicSemantic.value.transition.live_snapshot.next_pair_index >>> 15#usize=ok 0#u64 := shifted15
  rw [shifted,bind_tc_ok]
  have bit : lift (0#u64 &&& 1#u64)=ok 0#u64 := rfl
  rw [bit,bind_tc_ok]
  simp only [if_pos (by rfl : 0#u64=0#u64),bind_tc_ok,Aeneas.Std.uncurry]
  unfold empty_root pool_v1.pair_forest_semantic_terminal.constants.POOL_V1_PAIR_EMPTY_ROOTS_V1
  rfl
#print axioms step15
theorem step16 : validate_transition_loop JFu_PublicSemantic.value r16 1#usize=
    validate_transition_loop JFu_PublicSemantic.value r17 1#usize := by
  rw [validate_transition_loop,next16,bind_tc_ok]
  simp only [Aeneas.Std.uncurry,if_neg (by scalar_tac : ¬(16#usize=1#usize)),
    if_neg (by scalar_tac : ¬(16#usize<1#usize))]
  have shifted : JFu_PublicSemantic.value.transition.live_snapshot.next_pair_index >>> 16#usize=ok 0#u64 := shifted16
  rw [shifted,bind_tc_ok]
  have bit : lift (0#u64 &&& 1#u64)=ok 0#u64 := rfl
  rw [bit,bind_tc_ok]
  simp only [if_pos (by rfl : 0#u64=0#u64),bind_tc_ok,Aeneas.Std.uncurry]
  unfold empty_root pool_v1.pair_forest_semantic_terminal.constants.POOL_V1_PAIR_EMPTY_ROOTS_V1
  rfl
#print axioms step16
theorem step17 : validate_transition_loop JFu_PublicSemantic.value r17 1#usize=
    validate_transition_loop JFu_PublicSemantic.value r18 1#usize := by
  rw [validate_transition_loop,next17,bind_tc_ok]
  simp only [Aeneas.Std.uncurry,if_neg (by scalar_tac : ¬(17#usize=1#usize)),
    if_neg (by scalar_tac : ¬(17#usize<1#usize))]
  have shifted : JFu_PublicSemantic.value.transition.live_snapshot.next_pair_index >>> 17#usize=ok 0#u64 := shifted17
  rw [shifted,bind_tc_ok]
  have bit : lift (0#u64 &&& 1#u64)=ok 0#u64 := rfl
  rw [bit,bind_tc_ok]
  simp only [if_pos (by rfl : 0#u64=0#u64),bind_tc_ok,Aeneas.Std.uncurry]
  unfold empty_root pool_v1.pair_forest_semantic_terminal.constants.POOL_V1_PAIR_EMPTY_ROOTS_V1
  rfl
#print axioms step17
theorem step18 : validate_transition_loop JFu_PublicSemantic.value r18 1#usize=
    validate_transition_loop JFu_PublicSemantic.value r19 1#usize := by
  rw [validate_transition_loop,next18,bind_tc_ok]
  simp only [Aeneas.Std.uncurry,if_neg (by scalar_tac : ¬(18#usize=1#usize)),
    if_neg (by scalar_tac : ¬(18#usize<1#usize))]
  have shifted : JFu_PublicSemantic.value.transition.live_snapshot.next_pair_index >>> 18#usize=ok 0#u64 := shifted18
  rw [shifted,bind_tc_ok]
  have bit : lift (0#u64 &&& 1#u64)=ok 0#u64 := rfl
  rw [bit,bind_tc_ok]
  simp only [if_pos (by rfl : 0#u64=0#u64),bind_tc_ok,Aeneas.Std.uncurry]
  unfold empty_root pool_v1.pair_forest_semantic_terminal.constants.POOL_V1_PAIR_EMPTY_ROOTS_V1
  rfl
#print axioms step18
theorem step19 : validate_transition_loop JFu_PublicSemantic.value r19 1#usize=
    validate_transition_loop JFu_PublicSemantic.value r20 1#usize := by
  rw [validate_transition_loop,next19,bind_tc_ok]
  simp only [Aeneas.Std.uncurry,if_neg (by scalar_tac : ¬(19#usize=1#usize)),
    if_neg (by scalar_tac : ¬(19#usize<1#usize))]
  have shifted : JFu_PublicSemantic.value.transition.live_snapshot.next_pair_index >>> 19#usize=ok 0#u64 := shifted19
  rw [shifted,bind_tc_ok]
  have bit : lift (0#u64 &&& 1#u64)=ok 0#u64 := rfl
  rw [bit,bind_tc_ok]
  simp only [if_pos (by rfl : 0#u64=0#u64),bind_tc_ok,Aeneas.Std.uncurry]
  unfold empty_root pool_v1.pair_forest_semantic_terminal.constants.POOL_V1_PAIR_EMPTY_ROOTS_V1
  rfl
#print axioms step19
theorem done : validate_transition_loop JFu_PublicSemantic.value r20 1#usize=ok (.Ok ()) := by
  rw [validate_transition_loop]
  rfl
#print axioms done

theorem source : validate_transition_loop JFu_PublicSemantic.value r00 1#usize=ok (.Ok ()) := by
  rw [step00,step01,step02,step03,step04,step05,step06,step07,step08,step09,step10,step11,step12,step13,step14,step15,step16,step17,step18,step19,done]
#print axioms source
end AspisR1.JFu_TransitionSteps
end
