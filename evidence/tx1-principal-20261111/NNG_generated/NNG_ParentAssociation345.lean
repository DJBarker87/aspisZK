import NNG_AdmittedAssociation345
import NNG_Native345
set_option autoImplicit false
noncomputable section
namespace AspisR1.NNG_ParentAssociation345
open Aeneas Aeneas.Std Result NMT_345 NMT_CallTree NNG_Observed136

theorem byteRoute (s : Slice U8) (a b : U8) :
 ((LIB_Carriers.bytes s)==[byte a,byte b])=decide (s.val=[a,b]) := by
 rw [← NNG_DecoderGraph345.bytes]
 apply Bool.eq_iff_iff.mpr
 simp only [beq_iff_eq,decide_eq_true_eq]
 exact NNG_Compare345.projected _ _
#print axioms byteRoute

/-- Full emitted-parent association, including route guards, account count
and selection, every reached frame and the SAME child/returned checkpoint. -/
theorem source {W : Type} (s : Parent W) (env : RSL.Env) :
 NNG_Native345.producer s env=
 NNG_Model345.interpretation (NNG_ProjectFrames345.original s) env := by
 rw [NNG_Native345.source]
 have eq10 : (NNG_Calls345.calls env).c1 core.cmp.PartialEqU8 s.data
   (Array.make 2#usize [3#u8,10#u8])=ok (decide (s.data.val=[3#u8,10#u8])) :=
  NNG_Compare345.equal _ _
 have eq11 : (NNG_Calls345.calls env).c1 core.cmp.PartialEqU8 s.data
   (Array.make 2#usize [3#u8,11#u8])=ok (decide (s.data.val=[3#u8,11#u8])) :=
  NNG_Compare345.equal _ _
 unfold NNG_Tree345.tree
 rw [eq10]
 by_cases h10 : s.data.val=[3#u8,10#u8]
 · simp only [h10,decide_true]
   exact NNG_AdmittedAssociation345.source s env (Or.inl h10)
 · simp only [h10,decide_false]
   rw [eq11]
   by_cases h11 : s.data.val=[3#u8,11#u8]
   · simp only [h11,decide_true]
     exact NNG_AdmittedAssociation345.source s env (Or.inr h11)
   · simp only [h11,decide_false]
     have bad : RSL.TX1_345.badRoute (NNG_ProjectFrames345.original s)=true := by
      unfold RSL.TX1_345.badRoute
      change (!((LIB_Carriers.bytes s.data)==[3,10] || (LIB_Carriers.bytes s.data)==[3,11]) || _)=true
      rw [byteRoute s.data 3#u8 10#u8,byteRoute s.data 3#u8 11#u8]
      simp only [h10,h11,decide_false,Bool.false_or,Bool.not_false,Bool.true_or]
     unfold NNG_Model345.interpretation NNG_Phases345.run
     rw [bad]
     rfl
#print axioms source
end AspisR1.NNG_ParentAssociation345
