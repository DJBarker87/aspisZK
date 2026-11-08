import NNG_GeometryReturned094
import NNG_GeometryInverseCanonical094
import NNG_GeometryLineCanonical094
set_option autoImplicit false
noncomputable section
namespace AspisR1.NNG_GeometryFacts094
open Aeneas Aeneas.Std Result AspisR1Stage2

theorem word (flat : alloc.vec.Vec U32) (canonical : ∀ x∈flat.val,x.val<2147483647) (i : Nat) :
 (Port4C_GeometryGroups.word flat i).val<2147483647 := by
 unfold Port4C_GeometryGroups.word
 cases found : flat.val[i]? with
 | none=>exact (by decide : (0#u32).val<2147483647)
 | some x=>exact canonical x (List.mem_of_getElem? found)
#print axioms word

theorem lines (p : LIB_VCarriers.Prepared) (env : RSL.Env) (geo : LIB_VCarriers.Geo) (ev : List RSL.Event)
 (returned : LIBC_Geometry.child.run (p,0,10) env ⟨.ret (.ok geo),ev⟩) :
 ∀ x∈geo.line_z.val,x.val<2147483647 := by
 have source := NNG_GeometryReturned094.native p env geo ev returned
 obtain ⟨selected,order,bound,selection,run⟩ := Port4C_GeometryRange.accepted_range
  NFN_NEW_GeometryDictionary.adopted p.queries 0#usize 10#usize geo source
 have primitive := NFN_NEB_ActualGeometryModel.primitives
  NFN_NEW_GeometryRawInterface.ops NFN_NEW_GeometryDictionary.err
 have leaves : Port5Q1_GeometryCanonical.SessionAPrimitives NFN_NEW_GeometryDictionary.adopted :=
  ⟨primitive.point,primitive.line,primitive.multiply,primitive.double,primitive.one,primitive.subtract⟩
 have standard : Port4C_GeometryStd.install NFN_NEW_GeometryDictionary.adopted=
  NFN_NEW_GeometryDictionary.adopted := rfl
 rw [←standard] at run
 exact NNG_GeometryLineCanonical094.traversal NFN_NEW_GeometryDictionary.adopted leaves
  0#usize ⟨selected,0⟩ (alloc.vec.Vec.new U32) (alloc.vec.Vec.new U32) geo selected.val.length
  (by simp) (by simp [alloc.vec.Vec.new]) (by simp [alloc.vec.Vec.new]) run
#print axioms lines

/-- All geometry clauses consumed by the query child are derived from the
SAME successful geometry, including the initialized inverse buffer's frames. -/
theorem returned (p : LIB_VCarriers.Prepared) (env : RSL.Env) (geo : LIB_VCarriers.Geo) (ev : List RSL.Event)
 (success : LIBC_Geometry.child.run (p,0,10) env ⟨.ret (.ok geo),ev⟩) :
 geo.start=0#usize ∧ geo.inverses.val.length=10 ∧ geo.line_z.val.length=10 ∧
 (∀ row∈geo.inverses.val,∀ x∈row.val,x.val<2147483647) ∧
 (∀ x∈geo.line_z.val,x.val<2147483647) := by
 have source := NNG_GeometryReturned094.raw p env geo ev success
 obtain ⟨rows,line,flat,prefixes,product,suffix,resized,inverse,groups,nrows,hflat,hline,hstart,
  lineField,groupsField,hprefix,prefixSize,hinverse,hresize,hback,inverseSize,trace,collected,_,_,_,_⟩ :=
  NFN_NFB_GeometryComposed.accepted_physical p.queries 0#usize 10#usize (Or.inl ⟨rfl,rfl⟩)
   (fun _=>none) geo source
 have lineSize : line.val.length=10 := by
  rw [hline,List.length_map]
  exact nrows
 have inverses : ∀ x∈inverse.val,x.val<2147483647 :=
  NNG_GeometryInverseCanonical094.reverse flat.val prefixes.val trace (by
   rw [hresize]
   intro x member
   have equal : x=0#u32 := (List.mem_replicate.mp member).2
   rw [equal]
   decide)
 refine ⟨hstart,?_,?_,?_,lines p env geo ev success⟩
 · rw [collected,List.length_map,List.length_range,lineSize]
 · rw [lineField]
   exact lineSize
 · intro row member x inside
   rw [collected] at member
   obtain ⟨i,_,same⟩ := List.mem_map.mp member
   subst row
   change x∈[Port4C_GeometryGroups.word inverse (5*i),Port4C_GeometryGroups.word inverse (5*i+1),
    Port4C_GeometryGroups.word inverse (5*i+2),Port4C_GeometryGroups.word inverse (5*i+3),
    Port4C_GeometryGroups.word inverse (5*i+4)] at inside
   simp only [List.mem_cons,List.not_mem_nil,or_false] at inside
   rcases inside with rfl | rfl | rfl | rfl | rfl
   all_goals exact word inverse inverses _
#print axioms returned
end AspisR1.NNG_GeometryFacts094
