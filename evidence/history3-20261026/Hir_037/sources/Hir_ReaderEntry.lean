import Hir_InstalledReader
import Hist_ReaderAuthority
set_option autoImplicit false
noncomputable section
namespace AspisR1.Hir_ReaderEntry
open Aeneas Aeneas.Std Result Hist_Store Hist_RuntimeEntry S2W_D189Entry

theorem marker {F C : Type} (c : DrvC_Installation.Configuration F C)
    (store : Store) (layout : Layout) (id : S2W_ExtractionBoundary.Program)
    (data : Slice U8) (slot : S2W_ExtractionBoundary.Slot)
    (accepted : AdapterRw.r1_pool_adapter.owned.stage2_owned (DrvC_Installation.sdk c)
      id ((load store layout).second S2W_D189Wrappers.secondSizes) data slot = ok (.Ok ())) :
    Initialized (store (layout.handles 6).1).data := by
  obtain ⟨validated,pa,ca,raw,cp,pub,selected,finish,validation,proofIndex,cpIndex,proofRead,cpRead,encoding,range,child,length⟩ :=
    S2X.second_fixed_range (DrvC_Installation.sdk c) id _ data slot accepted
  have sameAccount := Result.ok.inj (cpIndex.symm.trans (Hist_SecondSnapshot.second_index (load store layout)))
  rw [sameAccount] at cpRead
  have bytes := Hist_SecondSnapshot.snapshot_bytes (DrvC_Installation.sdk c) (load store layout) 6 1768 1768 cp cpRead
  have same : cp = (store (layout.handles 6).1).data := Subtype.ext bytes
  rw [← same]
  exact Hir_InstalledReader.marker c (Array.to_slice pub) selected cp child

theorem owner {F C : Type} (c : DrvC_Installation.Configuration F C)
    (law : (DrvC_Installation.sdk c).op36 = Hist_Authority.keyEq)
    (store : Store) (layout : Layout) (id : S2W_ExtractionBoundary.Program)
    (data : Slice U8) (slot : S2W_ExtractionBoundary.Slot)
    (accepted : AdapterRw.r1_pool_adapter.owned.stage2_owned (DrvC_Installation.sdk c)
      id ((load store layout).second S2W_D189Wrappers.secondSizes) data slot = ok (.Ok ())) :
    (store (layout.handles 6).1).owner = id := by
  have original : AdapterRw.r1_pool_adapter.owned.stage2_owned (Hist_Authority.install (DrvC_Installation.sdk c))
      id ((load store layout).second S2W_D189Wrappers.secondSizes) data slot = ok (.Ok ()) := by
    simpa only [Hiq_KeyLaw.installed_eq _ law] using accepted
  obtain ⟨checkpoint,index,owner,rest⟩ := Hist_ReaderAuthority.accepted (DrvC_Installation.sdk c) id _ data slot original
  have same := Result.ok.inj (index.symm.trans (Hist_SecondSnapshot.second_index (load store layout)))
  subst checkpoint
  exact owner

#print axioms marker
#print axioms owner
end AspisR1.Hir_ReaderEntry
end
