#!/usr/bin/env python3
"""PCXW_: generate PRVEq_PIN2_ProbeSemanticPublicProjection.lean from the PIN2 probe emission's Types.lean.
usage: PCXW_mk_projection.py EMITTED_Types.lean GATE_Types.lean(FIq_NativeTypes sha cdc1db1e) OUT.lean
The emitted structure is copied field by field; every field type must equal the gate's field type after stripping the
emission namespace; the field list must equal the gate's plus exactly `destination : Option (Array Std.U8 32#usize)`."""
import re,sys,hashlib
em,gate,out=sys.argv[1:4]
E=open(em).read();G=open(gate).read()
def block(t):
    m=re.search(r'structure (\S*pool_v1\.pair_forest_semantic_terminal\.SemanticPublic) where\n((?:  .*\n)+)',t);assert m,'no SemanticPublic'
    fields=[tuple(x.strip() for x in l.split(' : ',1)) for l in m.group(2).splitlines()];return m.group(1),fields
en,ef=block(E);gn,gf=block(G)
assert [f[0] for f in gf]==['variant','pool','deployment_domain','anchor','nullifier','asset_id','recipient','change','withdrawal_amount','transition'],gf
assert [f[0] for f in ef]==['variant','pool','deployment_domain','anchor','nullifier','asset_id','recipient','change','withdrawal_amount','destination','transition'],ef
assert [f for f in ef if f[0]!='destination']==gf,'non-destination field types differ from the gate'
dest=[f for f in ef if f[0]=='destination'][0];assert dest[1]=='Option (Array Std.U8 32#usize)',dest
sha=lambda p:hashlib.sha256(open(p,'rb').read()).hexdigest()
lines=''.join('  %s : %s\n'%(a,b if a=='destination' else 'FIq_Native.'+b if False else b) for a,b in ef)
# gate field types are written unqualified inside `namespace FIq_Native`; qualify them for use outside it
def q(ty):
    ty=ty.replace('pool_v1.','FIq_Native.pool_v1.').replace('field.M31','FIq_Native.field.M31')
    return ty
fields=''.join('  %s : %s\n'%(a,q(b)) for a,b in ef)
open(out,'w').write(f'''-- PIN2 probe-crate SemanticPublic projection module (PCXW_). Probe crate aspis-r1-mask-extraction-probe (v4 merged source snapshot, archive sha256 870b9c10...),
-- with the PIN2 probe update PCXW_PROBE_UPDATE.diff (frozen r0 text at c7593d23fdc56fcee9a9df1628d5f63b52ac7a95; file sha256 see PCXW_PROBE_UPDATE.json).
-- Emission Types.lean sha256 {sha(em)}; gate FIq_NativeTypes.lean sha256 {sha(gate)}.
-- The PIN2 structure below is that emission's pool_v1.pair_forest_semantic_terminal.SemanticPublic, namespaced as PIN2P.SemanticPublic;
-- its field types are the gate's FIq_Native types (the emitted text of every field type other than `destination` is identical to the gate's).
import FIq_NativeTypes
open Aeneas Aeneas.Std
set_option maxHeartbeats 200000
set_option linter.dupNamespace false

namespace PIN2P

/-- PIN2 emission of aspis_r1_mask_extraction_probe::pool_v1::pair_forest_semantic_terminal::SemanticPublic: the old fields plus `destination`. -/
structure SemanticPublic where
{fields}
abbrev OldSP := FIq_Native.pool_v1.pair_forest_semantic_terminal.SemanticPublic

/-- Projection that drops `destination`. -/
def SemanticPublic.dropDestination (x : PIN2P.SemanticPublic) : OldSP :=
  {{ variant := x.variant, pool := x.pool, deployment_domain := x.deployment_domain, anchor := x.anchor,
    nullifier := x.nullifier, asset_id := x.asset_id, recipient := x.recipient, change := x.change,
    withdrawal_amount := x.withdrawal_amount, transition := x.transition }}

/-- Embedding that sets `destination := none`. -/
def SemanticPublic.embed (x : OldSP) : PIN2P.SemanticPublic :=
  {{ variant := x.variant, pool := x.pool, deployment_domain := x.deployment_domain, anchor := x.anchor,
    nullifier := x.nullifier, asset_id := x.asset_id, recipient := x.recipient, change := x.change,
    withdrawal_amount := x.withdrawal_amount, destination := none, transition := x.transition }}

/-- The PIN2 constructor, projected, is the old constructor on the same nine fields (destination carried but unused). -/
theorem SemanticPublic.dropDestination_mk (v p d a n i r c w dest t) :
    SemanticPublic.dropDestination (PIN2P.SemanticPublic.mk v p d a n i r c w dest t)
      = (FIq_Native.pool_v1.pair_forest_semantic_terminal.SemanticPublic.mk v p d a n i r c w t) := rfl

/-- `destination` does not influence the projection. -/
theorem SemanticPublic.dropDestination_set_destination (x : PIN2P.SemanticPublic) (d : Option (Array Std.U8 32#usize)) :
    SemanticPublic.dropDestination {{ x with destination := d }} = SemanticPublic.dropDestination x := rfl

theorem SemanticPublic.dropDestination_embed (x : OldSP) :
    SemanticPublic.dropDestination (SemanticPublic.embed x) = x := rfl

theorem SemanticPublic.embed_destination (x : OldSP) : (SemanticPublic.embed x).destination = none := rfl

theorem SemanticPublic.embed_dropDestination (x : PIN2P.SemanticPublic) :
    SemanticPublic.embed (SemanticPublic.dropDestination x) = {{ x with destination := none }} := rfl

/-- Two PIN2 values with equal projections and equal destinations are equal. -/
theorem SemanticPublic.eq_of_drop_eq (x y : PIN2P.SemanticPublic)
    (h : SemanticPublic.dropDestination x = SemanticPublic.dropDestination y) (hd : x.destination = y.destination) : x = y := by
  cases x; cases y
  simp only [SemanticPublic.dropDestination, OldSP, FIq_Native.pool_v1.pair_forest_semantic_terminal.SemanticPublic.mk.injEq] at h
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩ := h
  simp only at hd
  subst h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 hd
  rfl

end PIN2P

#print axioms PIN2P.SemanticPublic.dropDestination_mk
#print axioms PIN2P.SemanticPublic.dropDestination_set_destination
#print axioms PIN2P.SemanticPublic.dropDestination_embed
#print axioms PIN2P.SemanticPublic.embed_destination
#print axioms PIN2P.SemanticPublic.embed_dropDestination
#print axioms PIN2P.SemanticPublic.eq_of_drop_eq
''')
