import R1Z.PV_RunJoin_QuerySaltTotal64
import R1Z.PV_RunJoin_QueryEncodedTotal64
import R1Z.PV_RunJoin_QueryTail63
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_QueryTailTotal64
attribute [local irreducible] PV_RunJoin_WeightInstalled46.selected PV_B2_F_RawNative.selected PV_B2_F_ResourceFamilies.selected
set_option allowUnsafeReducibility true in
attribute [local irreducible] ProverRwP6BoundaryInstall.selected
open Aeneas Aeneas.Std Result ProverRwFull PV_RunJoin_WeightInstalled46

theorem append {n : Usize} (out : alloc.vec.Vec U8) (a : Array U8 n)
    (room : out.length+n.val≤Usize.max) :
    ∃ next, alloc.vec.Vec.extend_from_slice core.clone.CloneU8 out (Array.to_slice a)=ok next ∧
      next.length=out.length+n.val := by
  obtain ⟨next,hr,hv⟩ := PV_RunJoin_ByteAppend38.append out (Array.to_slice a)
    (by simpa only [Array.to_slice,Slice.length,a.property] using room)
  refine ⟨next,hr,?_⟩
  change next.val.length=out.val.length+n.val
  rw [hv,List.length_append,a.property]

theorem complete (base : ExternalTypes) (heap : Heap) (box : Box)
    (ops : @ExternalFuns (types base)) (cc1 cc2 : host_commitment.Commitment)
    (s1 s2 : host_commitment.PrivateSalts)
    (stored1 : cc1.private_salts=some s1) (stored2 : cc2.private_salts=some s2)
    (size1 : 262144≤s1.length) (size2 : 262144≤s2.length)
    (folded : Slice aspis_core.field.wide_exact.WideExact) (size : 262144≤folded.length)
    (salts : host_commitment.PrivateSalts) (saltSize : 65536≤salts.length)
    (u : aspis_core.r0.domain.FibreIndex) (bound : u.val<262144)
    (out : alloc.vec.Vec U8) (room : out.length+224≤Usize.max) :
    ∃ next, PV_RunJoin_QueryTail63.run base heap box ops cc1 cc2 u folded salts out=ok next ∧
      next.length=out.length+224 := by
  letI : ExternalTypes := types base
  letI : ExternalFuns := selected base heap box ops
  obtain ⟨salt1,h1⟩ := PV_RunJoin_QuerySaltTotal64.complete base heap box ops cc1 s1 stored1 size1 u bound
  obtain ⟨salt2,h2⟩ := PV_RunJoin_QuerySaltTotal64.complete base heap box ops cc2 s2 stored2 size2 u bound
  obtain ⟨out1,ho1,hl1⟩ := append out salt1 (by omega)
  obtain ⟨out2,ho2,hl2⟩ := append out1 salt2 (by omega)
  obtain ⟨encoded,he,hencoded⟩ := PV_RunJoin_QueryEncodedTotal64.complete base heap box ops folded size u bound
  obtain ⟨out3,ho3,hv3⟩ := PV_RunJoin_ByteAppend38.append out2 (alloc.vec.Vec.deref encoded)
    (by change out2.length+encoded.length≤Usize.max;omega)
  have hl3 : out3.length=out2.length+128 := by
    change out3.val.length=out2.val.length+128
    rw [hv3,List.length_append]
    change out2.val.length+encoded.length=out2.val.length+128
    rw [hencoded]
  obtain ⟨quarter,hquarter,hval⟩ := UScalar.div_spec u (y:=4#usize) (by decide)
  obtain ⟨salt4,h4⟩ := PV_RunJoin_QueryAccess64.salt salts quarter (by omega)
  obtain ⟨out4,ho4,hl4⟩ := append out3 salt4 (by omega)
  refine ⟨out4,?_,by omega⟩
  unfold PV_RunJoin_QueryTail63.run
  simp only [h1,h2,core.option.Option.unwrap,bind_tc_ok,ho1,ho2,he,ho3]
  change (do let quarter ← u/4#usize
             let salt ← host_commitment.PrivateSalts.get salts quarter
             alloc.vec.Vec.extend_from_slice core.clone.CloneU8 out3 (Array.to_slice salt))=ok out4
  simp only [hquarter,h4,bind_tc_ok,ho4]

#print axioms append
#print axioms complete
end R1Z.PV_RunJoin_QueryTailTotal64
