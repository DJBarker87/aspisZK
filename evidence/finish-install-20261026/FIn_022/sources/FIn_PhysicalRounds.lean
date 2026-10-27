import SAG_PhysicalShape
set_option autoImplicit false
namespace AspisR1.FIn_PhysicalRounds
open Aeneas Aeneas.Std Result

theorem rounds (ops : VTop_Stages.Ops) (proof : Slice U8) (t : Cons_Native.Witness)
    (shape : SAG_NativeFull.Shape ops proof t)
    (s0 : ops.op22=ok 7527#usize) (e0 : ops.op15=ok 7751#usize)
    (s1 : ops.op14=ok 7783#usize) (e1 : ops.op21=ok 8007#usize) :
    MultiproofConeCanonical.bytesOf t.v2.round0.val =
      OraclePortCompactDraft.slice (MultiproofConeCanonical.bytesOf proof.val) 7527 224 ∧
    MultiproofConeCanonical.bytesOf t.v2.round1.val =
      OraclePortCompactDraft.slice (MultiproofConeCanonical.bytesOf proof.val) 7783 224 := by
  obtain ⟨r0,folded,r1,fs,qs,h0,hfold,h1,hf,hq,read0,read1,readf⟩ := shape
  have a : r0=7527#usize := Result.ok.inj (h0.symm.trans s0)
  have b : folded=7751#usize := Result.ok.inj (hfold.symm.trans e0)
  have c : r1=7783#usize := Result.ok.inj (h1.symm.trans s1)
  have d : fs=8007#usize := Result.ok.inj (hf.symm.trans e1)
  subst r0; subst folded; subst r1; subst fs
  exact ⟨SAG_ViewBytes.region proof t.v2.round0 7527#usize 7751#usize read0,
    SAG_ViewBytes.region proof t.v2.round1 7783#usize 8007#usize read1⟩

#print axioms rounds
end AspisR1.FIn_PhysicalRounds
