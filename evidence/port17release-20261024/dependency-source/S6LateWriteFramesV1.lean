import S6PointWriteFrameV1
set_option autoImplicit false
namespace AspisS6SliceFrame

def late_header {T : Type} (magic : List T) (version count zero : T)
    (header snapshot afterstate total : List T) : List T :=
  (((((magic++[version])++[count])++header)++snapshot)++afterstate)++total++List.replicate 8 zero

theorem late_header_writes {T : Type} (magic : List T) (version count zero : T)
    (header snapshot afterstate total : List T)
    (hm : magic.length=8) (hh : header.length=2)
    (hs : snapshot.length=4) (ha : afterstate.length=4) (ht : total.length=4) :
    (((((((List.replicate 1520 zero).setSlice! 0 magic).set 8 version).set 9 count).setSlice! 10 header).setSlice! 12 snapshot).setSlice! 16 afterstate).setSlice! 20 total=
    late_header magic version count zero header snapshot afterstate total++List.replicate 1488 zero := by
  have h0 := setSlice_append_chunk [] magic 1520 zero (by rw [hm]; decide)
  simp only [List.length_nil,List.nil_append,hm,Nat.reduceSub] at h0
  rw [h0]
  have h1 := set_append_point magic 1511 zero version
  simp only [hm,Nat.reduceAdd] at h1
  rw [h1]
  have h2 := set_append_point (magic++[version]) 1510 zero count
  simp only [List.length_append,List.length_cons,List.length_nil,hm,Nat.reduceAdd] at h2
  rw [h2]
  have hc0 := setSlice_append_chunk ((magic++[version])++[count]) header 1510 zero (by rw [hh]; decide)
  simp only [List.length_append,List.length_cons,List.length_nil,hm,hh,hs,ha,ht,Nat.reduceAdd,Nat.reduceSub] at hc0
  rw [hc0]
  have hc1 := setSlice_append_chunk (((magic++[version])++[count])++header) snapshot 1508 zero (by rw [hs]; decide)
  simp only [List.length_append,List.length_cons,List.length_nil,hm,hh,hs,ha,ht,Nat.reduceAdd,Nat.reduceSub] at hc1
  rw [hc1]
  have hc2 := setSlice_append_chunk ((((magic++[version])++[count])++header)++snapshot) afterstate 1504 zero (by rw [ha]; decide)
  simp only [List.length_append,List.length_cons,List.length_nil,hm,hh,hs,ha,ht,Nat.reduceAdd,Nat.reduceSub] at hc2
  rw [hc2]
  have hc3 := setSlice_append_chunk (((((magic++[version])++[count])++header)++snapshot)++afterstate) total 1500 zero (by rw [ht]; decide)
  simp only [List.length_append,List.length_cons,List.length_nil,hm,hh,hs,ha,ht,Nat.reduceAdd,Nat.reduceSub] at hc3
  rw [hc3]
  unfold late_header
  simp only [List.append_assoc,←List.replicate_add]

theorem late_payload_writes {T : Type} (zero : T) (header snapshot afterstate : List T)
    (hh : header.length=32) (hs : snapshot.length=800) (ha : afterstate.length=688) :
    ((header++List.replicate 1488 zero).setSlice! 32 snapshot).setSlice! 832 afterstate=
      (header++snapshot)++afterstate := by
  have h0 := setSlice_append_chunk header snapshot 1488 zero (by rw [hs]; decide)
  simp only [hh,hs,Nat.reduceSub] at h0
  rw [h0]
  have h1 := setSlice_append_chunk (header++snapshot) afterstate 688 zero (by rw [ha])
  simp only [List.length_append,hh,hs,Nat.reduceAdd,ha,Nat.sub_self,List.replicate_zero,List.append_nil] at h1
  exact h1

#print axioms late_header_writes
#print axioms late_payload_writes
end AspisS6SliceFrame
