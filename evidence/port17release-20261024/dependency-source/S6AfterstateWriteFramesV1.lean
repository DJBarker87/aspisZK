import S6PointWriteFrameV1
set_option autoImplicit false
namespace AspisS6SliceFrame

theorem afterstate_header_writes {T : Type} (magic : List T) (hmagic : magic.length=4)
    (zero version format encoding success : T) :
    (((((List.replicate 688 zero).setSlice! 0 magic).set 4 version).set 5 format).set 6 encoding).set 7 success =
      (magic++[version,format,encoding,success])++List.replicate 680 zero := by
  have h0 := setSlice_append_chunk [] magic 688 zero (by rw [hmagic]; decide)
  simp only [List.length_nil,List.nil_append,hmagic,Nat.reduceSub] at h0
  rw [h0]
  have h1 := set_append_point (magic) 683 zero version
  simp only [List.length_append,List.length_cons,List.length_nil,hmagic,Nat.reduceAdd] at h1
  rw [h1]
  have h2 := set_append_point (magic++[version]) 682 zero format
  simp only [List.length_append,List.length_cons,List.length_nil,hmagic,Nat.reduceAdd] at h2
  rw [h2]
  have h3 := set_append_point (magic++[version]++[format]) 681 zero encoding
  simp only [List.length_append,List.length_cons,List.length_nil,hmagic,Nat.reduceAdd] at h3
  rw [h3]
  have h4 := set_append_point (magic++[version]++[format]++[encoding]) 680 zero success
  simp only [List.length_append,List.length_cons,List.length_nil,hmagic,Nat.reduceAdd] at h4
  rw [h4]
  simp only [List.append_assoc,List.cons_append,List.nil_append,List.singleton_append]

theorem afterstate_prefix_chunks {T : Type} (zero : T) (header index root : List T)
    (hheader : header.length=8) (hindex : index.length=8) (hroot : root.length=32) :
    ((header++List.replicate 680 zero).setSlice! 8 index).setSlice! 16 root=
      (header++index++root)++List.replicate 640 zero := by
  have h0 := setSlice_append_chunk header index 680 zero (by rw [hindex]; decide)
  simp only [hheader,hindex,Nat.reduceSub] at h0
  rw [h0]
  have h1 := setSlice_append_chunk (header++index) root 672 zero (by rw [hroot]; decide)
  simp only [List.length_append,hheader,hindex,Nat.reduceAdd,hroot,Nat.reduceSub] at h1
  exact h1

#print axioms afterstate_header_writes
#print axioms afterstate_prefix_chunks
end AspisS6SliceFrame
