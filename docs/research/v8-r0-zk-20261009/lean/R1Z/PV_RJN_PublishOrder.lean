import R1Z.PV_RJN_PublishTrace
import R1Z.PV_RJN_Producers
set_option autoImplicit false
namespace R1Z.PV_RJN_PublishOrder
open Aeneas Aeneas.Std Result ProverRwFull PV_RunJoin_PublishSkeleton54
open PV_RunJoin_PublishSkeleton57 (QueryRange)
open PV_RunJoin_PublishContext57 (QueryContext)
open PV_RJN_Producers
variable [ExternalTypes] [ExternalFuns]

theorem actual {I : Type} (runs : I → Run)
    (layout : PV_RJN_Producer_Layout runs) (room : PV_RJN_Producer_FrontRoom runs) :
    PV_RunJoin_PublishContext57.PV_RunJoin_Link_PublishOrder runs := by
  intro query node i p proof fields range context success
  obtain ⟨sz,op,nd,mg,tg,hsz,hop,hnd,hmg,htg,hpsize,hpop,hpnd,hheader⟩ := layout i
  obtain ⟨size,openings,nodes,magic,tag,h0,h1,h2,h3,h4,h5,h6,h7,h8,h9,ib,cc1,cc2,semanticResult,valuesResult,
    hsize,hmagic,htag,hh0,hh1,hsem,hclaim,hib,hh4,hh5,hh6,hh7,hh8,hopen,hopenlen,
    hc1,hc2,hh9,hnodes,hnodelen,hn,hprooflen⟩ := PV_RJN_PublishTrace.source .S2 p proof success
  have esz := Result.ok.inj (hsz.symm.trans hsize)
  have eop := Result.ok.inj (hop.symm.trans hopen)
  have end1 := Result.ok.inj (hnd.symm.trans hnodes)
  have emg := Result.ok.inj (hmg.symm.trans hmagic)
  have etg := Result.ok.inj (htg.symm.trans htag)
  subst sz; subst op; subst nd; subst mg; subst tg
  have h0bytes : bytes h0.val=bytes magic.val := by
    have h := PV_RJN_Bytes.append_success _ _ _ hh0
    change h0.val=[]++magic.val at h
    simpa only [List.nil_append] using congrArg bytes h
  have h1bytes : bytes h1.val=(runs i).plan.header := by
    have h := congrArg bytes (PV_RJN_Bytes.append_success _ _ _ hh1)
    rw [PV_RJN_Bytes.append,h0bytes] at h
    exact h.trans hheader.symm
  obtain ⟨hc0,hc1bytes,hfbytes,hsemantic,hvalues,hroot,hinactive⟩ := fields
  have len1 : h1.val.length=(runs i).plan.header.length := by
    rw [← PV_RJN_Bytes.length h1.val,h1bytes]
  have room1 : h1.length+(runs i).plan.semantic.length≤Usize.max := by
    change h1.val.length+_≤_
    have := room i
    omega
  obtain ⟨s,hs,hsv⟩ := hsemantic h1 room1
  have he : s=h2 := by
    have := Result.ok.inj (hs.symm.trans hsem)
    exact Prod.mk.inj this |>.2
  subst s
  have h2bytes : bytes h2.val=(runs i).plan.header++(runs i).plan.semantic := by
    rw [hsv,h1bytes]
  have len2 : h2.val.length=(runs i).plan.header.length+(runs i).plan.semantic.length := by
    rw [← PV_RJN_Bytes.length h2.val,h2bytes,List.length_append]
  have room2 : h2.length+(runs i).plan.claim.length≤Usize.max := by
    change h2.val.length+_≤_
    rw [len2]
    exact room i
  obtain ⟨s,hs,hsv⟩ := hvalues h2 room2
  have he : s=h3 := by
    have := Result.ok.inj (hs.symm.trans hclaim)
    exact Prod.mk.inj this |>.2
  subst s
  have h3bytes : bytes h3.val=(runs i).plan.header++(runs i).plan.semantic++(runs i).plan.claim := by
    rw [hsv,h2bytes]
  obtain ⟨ib',hib',hibv⟩ := hinactive
  have eib := Result.ok.inj (hib'.symm.trans hib)
  subst ib'
  have h4bytes := congrArg bytes (PV_RJN_Bytes.append_success _ _ _ hh4)
  have h5bytes := congrArg bytes (PV_RJN_Bytes.append_success _ _ _ hh5)
  have h6bytes := congrArg bytes (PV_RJN_Bytes.append_success _ _ _ hh6)
  have h7bytes := congrArg bytes (PV_RJN_Bytes.append_success _ _ _ hh7)
  have h8bytes := congrArg bytes (PV_RJN_Bytes.append_success _ _ _ hh8)
  have frontbytes : bytes h8.val=front (runs i) := by
    simp only [PV_RJN_Bytes.append] at h4bytes h5bytes h6bytes h7bytes h8bytes
    change bytes h4.val=bytes h3.val++bytes ib.val at h4bytes
    change bytes h5.val=bytes h4.val++bytes p.c0bytes.val at h5bytes
    change bytes h6.val=bytes h5.val++bytes p.root.val at h6bytes
    change bytes h7.val=bytes h6.val++bytes p.c1bytes.val at h7bytes
    change bytes h8.val=bytes h7.val++bytes p.fbytes.val at h8bytes
    rw [h8bytes,h7bytes,h6bytes,h5bytes,h4bytes,h3bytes,hibv,hc0,hc1bytes,hfbytes,hroot]
    rfl
  have offopen : h8.length=(runs i).plan.offOpenings := by rw [hpop]; exact congrArg UScalar.val hopenlen
  obtain ⟨_,hq⟩ := query i p fields range context
  obtain ⟨q,hq,hqv⟩ := hq h8 cc1 cc2 hc1 hc2 offopen
  have eq := Result.ok.inj (hq.symm.trans hh9)
  subst q
  have querybytes : ProverCommitPublish43.queries (runs i).plan.queries (front (runs i))=bytes h9.val := by
    rw [← frontbytes]
    exact hqv.symm
  have offnode : h9.length=(runs i).plan.offNodes := by rw [hpnd]; exact congrArg UScalar.val hnodelen
  have model := (node i p fields).2.2 h9 cc1 cc2 hc1 hc2 offnode
  rw [hn] at model
  change some (bytes proof.val)=exceptBytes _ at model
  have slots : ProverCommitPublish43.slots (runs i).plan.slots (bytes h9.val)=.ok (bytes proof.val) := by
    cases hs : ProverCommitPublish43.slots (runs i).plan.slots (bytes h9.val) with
    | error e => rw [hs] at model; cases model
    | ok b =>
      rw [hs] at model
      have hb := Option.some.inj model
      exact congrArg Except.ok hb.symm ▸ hs
  have nodeLen : (bytes h9.val).length=(runs i).plan.offNodes := by
    rw [PV_RJN_Bytes.length]
    exact offnode
  have proofLen : (bytes proof.val).length=(runs i).plan.proofBytes := by
    rw [PV_RJN_Bytes.length,hpsize]
    exact congrArg UScalar.val hprooflen
  rw [ProverCommitPublish43.assemble_loop]
  simp only [ProverCommitPublish43.assemble,Except.bind,querybytes,nodeLen,ne_eq,not_true_eq_false,if_false,
    slots,proofLen]

#print axioms actual
end R1Z.PV_RJN_PublishOrder
