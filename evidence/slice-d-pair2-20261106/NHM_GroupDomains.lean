import NHM_GroupRoot
import NHM_LoopDomain
set_option autoImplicit false
namespace NHM_GroupDomains
open Aeneas Aeneas.Std Result AspisR1 LPi_FieldValues

theorem reached (n : Nat) (iter next : NHI_RangeProgress.Range) (j : Usize)
 (last : iter.end.val=n)
 (run : core.iter.range.IteratorRange.next core.iter.range.StepUsize iter=ok (some j,next)) : j.val<n := by
 obtain ⟨same,he,hi,active⟩:=NHI_RangeProgress.some_next iter next j run
 subst j
 omega

theorem group (j : Usize) (g : U8)
 (read : Array.index_usize FIo_Native.weights.S2_INACTIVE_GROUPS j=ok g) :
 g.val<12 ∧ (UScalar.cast .Usize g).val=g.val := by
 have small:=NHM_ArrayCanon.read (fun x : U8=>x.val<12)
  FIo_Native.weights.S2_INACTIVE_GROUPS j g NHI_GroupTables.bounded_entries read
 refine ⟨small,?_⟩
 scalar_tac

theorem coefficient_args (f : Slice U8) (j : Usize) (small : j.val<64)
 (cells : NHM_GroupCoefficient.Cells) (cc : ∀ x∈cells.val,canonE x)
 (g : U8) (before value : NE)
 (hg : Array.index_usize FIo_Native.weights.S2_INACTIVE_GROUPS j=ok g)
 (hb : Array.index_usize cells (UScalar.cast .Usize g)=ok before)
 (hv : FIo_Native.weights.field f j=ok value) :
 (UScalar.cast .Usize g).val<12 ∧ canonE before ∧ canonE value := by
 obtain ⟨bound,castEq⟩:=group j g hg
 exact ⟨by omega,NHM_ArrayCanon.read canonE cells _ before cc hb,
  NHE_FieldCanonical.success f j small value hv⟩

theorem coefficient_all (f : Slice U8) :
 NHM_LoopDomain.all (NHM_GroupCoefficient.body f) NHM_GroupCoefficientDomain.Inv 65
  ({start:=0#usize,«end»:=64#usize},NHM_GroupRoot.initial) :=
 NHM_LoopDomain.invariant _ _ (NHM_GroupCoefficientDomain.preserves f) _ _
  ⟨rfl,by change (0:Nat)≤64;omega,NHM_GroupRoot.initial_canonical⟩

def WeightInv (s : NHM_GroupWeight.State) : Prop :=
 s.1.end.val=16 ∧ s.1.start.val≤16 ∧ canonE s.2

theorem weight_preserves (low : Array NE 16#usize) (hl : ∀ x∈low.val,canonE x)
 (g : Usize) (s t : NHM_GroupWeight.State) (h : WeightInv s)
 (run : NHM_GroupWeight.body low g s=ok (.cont t)) : WeightInv t := by
 obtain ⟨last,bound,canon⟩:=h
 obtain ⟨he,hi,active⟩:=NHM_GroupWeight.progress low g s t run
 have hev:=congrArg (fun x : Usize=>x.val) he
 exact ⟨by omega,by omega,NHM_GroupWeightDomain.preserves low hl g s t canon run⟩

theorem weight_all (low : Array NE 16#usize) (hl : ∀ x∈low.val,canonE x) (g : Usize) :
 NHM_LoopDomain.all (NHM_GroupWeight.body low g) WeightInv 17
  ({start:=0#usize,«end»:=16#usize},NHI_Scalar.zero) :=
 NHM_LoopDomain.invariant _ _ (weight_preserves low hl g) _ _
  ⟨rfl,by change (0:Nat)≤16;omega,NHI_Scalar.zero_canonical⟩

def AccumInv (s : NHM_GroupAccum.State) : Prop :=
 s.1.end.val=12 ∧ s.1.start.val≤12 ∧ canonE s.2

theorem accum_preserves (low : Array NE 16#usize) (hl : ∀ x∈low.val,canonE x)
 (cells : NHM_GroupCoefficient.Cells) (hc : ∀ x∈cells.val,canonE x)
 (s t : NHM_GroupAccum.State) (h : AccumInv s)
 (run : NHM_GroupAccum.body low cells s=ok (.cont t)) : AccumInv t := by
 obtain ⟨last,bound,canon⟩:=h
 obtain ⟨he,hi,active⟩:=NHM_GroupAccum.progress low cells s t run
 have hev:=congrArg (fun x : Usize=>x.val) he
 exact ⟨by omega,by omega,NHM_GroupAccumDomain.preserves low hl cells hc s t canon run⟩

theorem accum_all (low : Array NE 16#usize) (hl : ∀ x∈low.val,canonE x)
 (cells : NHM_GroupCoefficient.Cells) (hc : ∀ x∈cells.val,canonE x) :
 NHM_LoopDomain.all (NHM_GroupAccum.body low cells) AccumInv 13
  ({start:=0#usize,«end»:=12#usize},NHI_Scalar.zero) :=
 NHM_LoopDomain.invariant _ _ (accum_preserves low hl cells hc) _ _
  ⟨rfl,by change (0:Nat)≤12;omega,NHI_Scalar.zero_canonical⟩

#print axioms reached
#print axioms group
#print axioms coefficient_args
#print axioms coefficient_all
#print axioms weight_preserves
#print axioms weight_all
#print axioms accum_preserves
#print axioms accum_all
end NHM_GroupDomains
