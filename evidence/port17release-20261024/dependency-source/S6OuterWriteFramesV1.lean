import S6PointWriteFrameV1
set_option autoImplicit false
namespace AspisS6SliceFrame

theorem forest_header_writes {T : Type} (magic : List T) (hm : magic.length=4)
    (zero version kind encoding lane : T) :
    (((((List.replicate 1880 zero).setSlice! 0 magic).set 4 version).set 5 kind).set 6 encoding).set 7 lane =
      (magic++[version,kind,encoding,lane])++List.replicate 1872 zero := by
  have h0 := setSlice_append_chunk [] magic 1880 zero (by rw [hm]; decide)
  simp only [List.length_nil,List.nil_append,hm,Nat.reduceSub] at h0
  rw [h0]
  have h1 := set_append_point (magic) 1875 zero version
  simp only [List.length_append,List.length_cons,List.length_nil,hm,Nat.reduceAdd] at h1
  rw [h1]
  have h2 := set_append_point ((magic++[version])) 1874 zero kind
  simp only [List.length_append,List.length_cons,List.length_nil,hm,Nat.reduceAdd] at h2
  rw [h2]
  have h3 := set_append_point (((magic++[version])++[kind])) 1873 zero encoding
  simp only [List.length_append,List.length_cons,List.length_nil,hm,Nat.reduceAdd] at h3
  rw [h3]
  have h4 := set_append_point ((((magic++[version])++[kind])++[encoding])) 1872 zero lane
  simp only [List.length_append,List.length_cons,List.length_nil,hm,Nat.reduceAdd] at h4
  rw [h4]
  simp only [List.append_assoc,List.cons_append,List.nil_append]

theorem forest_common_writes {T : Type} (zero : T)
    (header master checkpoint selected sequence anchor : List T)
    (hh : header.length=8) (hm : master.length=32) (hc : checkpoint.length=32)
    (hs : selected.length=32) (hq : sequence.length=8) (ha : anchor.length=32) :
    (((((header++List.replicate 1872 zero).setSlice! 8 master).setSlice! 40 checkpoint).setSlice! 72 selected).setSlice! 104 sequence).setSlice! 112 anchor =
      (((((header++master)++checkpoint)++selected)++sequence)++anchor)++List.replicate 1736 zero := by
  have h0 := setSlice_append_chunk (header) master 1872 zero (by rw [hm]; decide)
  simp only [List.length_append,hh,hm,hc,hs,hq,ha,Nat.reduceAdd,Nat.reduceSub] at h0
  rw [h0]
  have h1 := setSlice_append_chunk ((header++master)) checkpoint 1840 zero (by rw [hc]; decide)
  simp only [List.length_append,hh,hm,hc,hs,hq,ha,Nat.reduceAdd,Nat.reduceSub] at h1
  rw [h1]
  have h2 := setSlice_append_chunk (((header++master)++checkpoint)) selected 1808 zero (by rw [hs]; decide)
  simp only [List.length_append,hh,hm,hc,hs,hq,ha,Nat.reduceAdd,Nat.reduceSub] at h2
  rw [h2]
  have h3 := setSlice_append_chunk ((((header++master)++checkpoint)++selected)) sequence 1776 zero (by rw [hq]; decide)
  simp only [List.length_append,hh,hm,hc,hs,hq,ha,Nat.reduceAdd,Nat.reduceSub] at h3
  rw [h3]
  have h4 := setSlice_append_chunk (((((header++master)++checkpoint)++selected)++sequence)) anchor 1768 zero (by rw [ha]; decide)
  simp only [List.length_append,hh,hm,hc,hs,hq,ha,Nat.reduceAdd,Nat.reduceSub] at h4
  rw [h4]

theorem forest_payload_writes {T : Type} (zero : T) (common late payment : List T)
    (hc : common.length=144) (hl : late.length=1520) (hp : payment.length=216) :
    ((common++List.replicate 1736 zero).setSlice! 144 late).setSlice! 1664 payment =
      (common++late)++payment := by
  have h0 := setSlice_append_chunk common late 1736 zero (by rw [hl]; decide)
  simp only [hc,hl,Nat.reduceSub] at h0
  rw [h0]
  have h1 := setSlice_append_chunk (common++late) payment 216 zero (by rw [hp])
  simp only [List.length_append,hc,hl,Nat.reduceAdd,hp,Nat.sub_self,List.replicate_zero,List.append_nil] at h1
  exact h1

#print axioms forest_header_writes
#print axioms forest_common_writes
#print axioms forest_payload_writes
end AspisS6SliceFrame
