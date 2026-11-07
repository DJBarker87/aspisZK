import LIB_VRecordsAll
set_option autoImplicit false
noncomputable section
namespace LIB_VRecordDomains
open Aeneas Aeneas.Std LIB_VCarriers
open AspisR1 AspisR1PublicPreparation
theorem host_raw {A E : Type} (r : Except E A) : LIB_VRecords.host (LIB_VRecords.raw r)=r := by cases r <;> rfl
theorem record (p : Prefix) (slot : Fin 27) :
 ∃ r,LIB_VRecords.validatedRecord p slot.val=.ok r ∧
 r.row=NJM_InvocationRoots.row slot ∧ r.framed.val.length=NGX_PrefixGeometry.width slot.val := by
 obtain ⟨r,getter,tag,geometry⟩ := NIX_ProducerInstall.framed p.source p.parsed p.parse_eq
  (NJM_InvocationRoots.row slot) slot.isLt
 have native := LIB_VRecords.validated_exact p (NJM_InvocationRoots.row slot)
 have result := Result.ok.inj (native.symm.trans getter)
 have host := congrArg LIB_VRecords.host result
 rw [host_raw] at host
 exact ⟨r,host,tag,geometry⟩
theorem extra (p : Prefix) :
 ∃ r,LIB_VRecords.validatedRecord p 25=.ok r ∧ LIB_VDecode.Domain r 87 := by
 obtain ⟨r,getter,tag,geometry⟩ := record p ⟨25,by omega⟩
 refine ⟨r,getter,?_,?_⟩
 · rw [tag];exact NGO_CallerDomains.Call.extra
 · rw [geometry,tag];rfl
theorem beforeZ1 (p : Prefix) :
 ∃ r,LIB_VRecords.validatedRecord p 26=.ok r ∧ LIB_VDecode.Domain r 0 := by
 obtain ⟨r,getter,tag,geometry⟩ := record p ⟨26,by omega⟩
 refine ⟨r,getter,?_,?_⟩
 · rw [tag];exact NGO_CallerDomains.Call.beforeZ1
 · rw [geometry,tag];rfl
theorem payload2 (p : Prefix) :
 ∃ bytes,LIB_VRecords.payload p 2=.ok bytes ∧ bytes.length=32 := by
 obtain ⟨r,getter,tag,geometry⟩ := NIX_ProducerInstall.framed p.source p.parsed p.parse_eq 2#u8 (by decide)
 obtain ⟨bytes,tail,same,length⟩ := NGX_Payload.tail_total r.framed (by
  rw [geometry];exact (NGX_PrefixGeometry.widths 2).1)
 have selected := LIB_VRecords.selected_of_validated (prefixRaw p) 2#u8 r getter
 have raw : FinishModel.payload (prefixRaw p) 2#u8=.ok (.Ok bytes) := by
  rw [NGX_Payload.source,selected]
  exact tail
 have exact_ := LIB_VRecordsAll.payload_native p 2#u8
 rw [raw,bind_tc_ok] at exact_
 refine ⟨LIB_Carriers.bytes bytes,(Result.ok.inj exact_).symm,?_⟩
 rw [NMS_R2N_RSLScalars.bytes_length,length,geometry]
 rfl
#print axioms host_raw
#print axioms record
#print axioms extra
#print axioms beforeZ1
#print axioms payload2
end LIB_VRecordDomains
