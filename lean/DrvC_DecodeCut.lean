import DrvC_NativeDecode
import DrvC_AcceptedCalls
set_option autoImplicit false
noncomputable section
namespace AspisR1.DrvC_DecodeCut
open Aeneas Aeneas.Std Result
open DrvC_Installation S2W_NativeConsolidation MultiproofConeCanonical

theorem cancel {A : Type} (initial xs ys : List A) (h : initial ++ xs = initial ++ ys) : xs = ys := by
  induction initial with
  | nil => exact h
  | cons a rest ih => exact ih (List.cons.inj h).2

theorem same_cut {F C : Type} (c : Configuration F C)
    (program : S2W_ExtractionBoundary.Program)
    (accounts1 accounts2 : S2W_ExtractionBoundary.Accounts) (data : Slice U8)
    (saved : alloc.vec.Vec U8) (f : FirstCut) (s : SecondCut)
    (accepted : AdapterRw.r1_pool_adapter.owned.stage1_owned (sdk c) program accounts1 data = ok (.Ok saved))
    (cuts : SourceCuts (sdk c) accounts1 accounts2 saved f s) :
    ∃ semantic, Port1_Driver.decodeSemantic (sdk c) f.pub = ok (some semantic) ∧
      SourceCuts (sdk c) accounts1 accounts2 saved {f with semantic := semantic} s := by
  obtain ⟨pa,pu,pub,raw,stmt,semantic,proof,split,hpa,hpu,hraw,hpub,hd,hvalid,hsem,range,first,len⟩ :=
    DrvC_NativeDecode.first_call_decoded (sdk c) program accounts1 data saved accepted
  have pae : pa = f.proofAccount := Result.ok.inj (hpa.symm.trans cuts.proof1Index)
  have pue : pu = f.publicAccount := Result.ok.inj (hpu.symm.trans cuts.public1Index)
  subst pa
  subst pu
  have rawe : raw = f.raw := core.result.Result.Ok.inj (Result.ok.inj (hraw.symm.trans cuts.proof1Read))
  have pube : pub = f.pub := core.result.Result.Ok.inj (Result.ok.inj (hpub.symm.trans cuts.public1Read))
  subst raw
  subst pub
  have shapes := AdapterRw.Ranges.suffix_exact f.raw proof 688#usize 58295#usize
    (by scalar_tac) (by simpa using len) range
  have start : (688#usize : Usize).val = 688 := by scalar_tac
  have suffix : bytesOf f.raw.val = (bytesOf f.raw.val).take 688 ++ bytesOf proof.val := by
    simpa only [bytesOf,List.map_append,List.map_take,start] using congrArg bytesOf shapes.2
  have pe := DrvC_Bytes.slice_injective proof f.proof (cancel _ _ _ (suffix.symm.trans cuts.firstSuffix))
  subst proof
  have sp := (DrvC_AcceptedCalls.split c semantic f.pub f.proof split saved first).trans
    (DrvC_AcceptedCalls.split c f.semantic f.pub f.proof f.split saved cuts.first).symm
  rw [sp] at first
  refine ⟨semantic,?_,{cuts with first := first}⟩
  simp only [Port1_Driver.decodeSemantic,hd,hvalid,hsem,bind_tc_ok]

#print axioms cancel
#print axioms same_cut
end AspisR1.DrvC_DecodeCut
end
