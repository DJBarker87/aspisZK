"""Per-function index arithmetic targets, preserving exact LLBC source spans.
These are arithmetic prerequisites: source-to-event and caller certificates remain
separate. No row is promoted to a full source binding by this generator.
"""
from pathlib import Path
import json,hashlib,os
D=Path(os.environ.get('PV_B3Q_OUTPUT','evidence/pv-b3q2-20261031'));O=D/'lean';x=json.loads(Path('evidence/pv-b3q2-20261031/index-obligations.json').read_text())
# Header, proposition, and predecessor proof for each genuinely dynamic shape.
C={
0:('(i : Nat) (h : Emitted 84 i)','i / 28 < 3 ∧ i % 28 < 29 ∧ i < 84','have b := h.2\n  omega'),
6:('(column maskColumn before24 before4 : Nat) (h16 : Emitted 16 column) (h10 : Emitted 10 maskColumn) (h24 : before24 ≤ 24) (p24 : 0 < before24) (h4 : before4 ≤ 4) (p4 : 0 < before4)','column < 16 ∧ maskColumn < 10 ∧ 16+maskColumn < 28 ∧ before24-1 < 24 ∧ before4-1 < 4','have b := h16.2\n  have c := h10.2\n  omega'),
8:('(i : Nat) (h : Emitted 10 i)','i < 10','exact h.2'),
13:('(level : Nat) (h : Emitted 20 level)','level < 20 ∧ level < 64','have b := h.2\n  omega'),
14:('(point column : Nat) (hp : point < 3) (hc : column < 28)','point*28+column < 84','omega'),
20:('(linkIndex : Nat) (h : Emitted 136 linkIndex)','linkIndex < 136','exact h.2'),
38:('(level : Nat) (h : Reach 0 20 level)','level < 21','have b := reach_invariant h\n  omega'),
42:('(lower upper index : Nat) (h : Reach lower upper index) (active : index < upper) (caller : upper ≤ 64)','index < 64','omega'),
47:('(lane : Nat) (h : Emitted 16 lane)','lane < 16','exact h.2'),
55:('(rangeIndex conserveIndex : Nat) (hr : Emitted 10 rangeIndex) (hc : Emitted 10 conserveIndex)','rangeIndex < 16 ∧ 10+rangeIndex < 33 ∧ conserveIndex < 16 ∧ 20+conserveIndex < 33','have r := hr.2\n  have c := hc.2\n  omega'),
57:('(level carry : Nat) (h : Emitted 20 level) (branch : carry < 20)','level < 20 ∧ carry < 20 ∧ 34+level < 64','have b := h.2\n  omega'),
58:('(start count group slot : Nat) (shape : 0 < count ∧ start+count ≤ 96) (groupBound : group ≤ (start+count-1)/4) (slotBound : slot < 4) (inside : start ≤ 4*group+slot ∧ 4*group+slot < start+count)','group < 24 ∧ slot < 4 ∧ 4*group+slot-start < count','exact preweighted_source start count group slot shape groupBound slotBound inside'),
60:('(row : Nat) (h : row < 1024)','row/16 < 64 ∧ row%16 < 16','exact PV_B3Q_PanicGuards.endpoint_selector_bounds row h'),
69:('(link : PV_B3Q_FrozenTables.Link) (h : link ∈ PV_B3Q_FrozenTables.links)','link.2.2.1.2.1 < 2 ∧ link.2.2.1.2.2 < 14 ∧ link.2.2.2.2.1 < 2 ∧ link.2.2.2.2.2 < 14','have b := PV_B3Q_FrozenTables.link_member_safe link h\n  omega'),
185:('(coordinate len index : Nat) (h : PV_B3Q_ExpandGuards.Stage 0 coordinate len) (outer : coordinate < 6) (inner : index < len)','coordinate < 10 ∧ index < 64 ∧ 2*index < 64 ∧ 2*index+1 < 64','exact PV_B3Q_ExpandGuards.high_inner coordinate len index h outer inner'),
212:('(group output index : Nat) (hg : Emitted 4 group) (ho : Emitted 4 output) (hi : Emitted 16 index)','4*group < 16 ∧ 4*group+1 < 16 ∧ 4*group+2 < 16 ∧ 4*group+3 < 16 ∧ 4*group+output < 16 ∧ index < 16','have g := hg.2\n  have o := ho.2\n  have i := hi.2\n  omega'),
213:('(lane : Nat) (h : Emitted 16 lane)','lane < 16','exact h.2'),
214:('(lane : Nat) (h : Emitted 16 lane)','lane < 16','exact h.2'),
215:('(lane : Nat) (h : Emitted 16 lane)','lane < 16','exact h.2'),
216:('(lane : Nat) (h : Emitted 16 lane)','lane < 16','exact h.2'),
217:('(lane : Nat) (h : Emitted 16 lane)','lane < 16','exact h.2'),
218:('(start index finish limb : Nat) (outer : start < finish) (inner : start ≤ index) (guard : index < min (start+4) finish) (limbGuard : Emitted 4 limb)','index < finish ∧ index-start < 4 ∧ limb < 4','have b := chunk_bounds start index finish outer inner guard\n  exact ⟨b.1,b.2,limbGuard.2⟩'),
223:('(lane : Nat) (h : Emitted 16 lane)','lane < 16 ∧ 8 < 16 ∧ 8+1 < 16','have b := h.2\n  omega'),
224:('(lane : Nat) (h : Emitted 8 lane)','1+lane < 16 ∧ lane < 16 ∧ 1+lane < 17 ∧ 8+lane < 16 ∧ 1+8+lane < 17','have b := h.2\n  omega'),
226:('(before : Nat) (h : before ≤ 9) (positive : 0 < before)','before-1 < 16','omega'),
231:('(lane : Nat) (h : Emitted 8 lane)','2+lane < 16 ∧ 3+lane < 12','have b := h.2\n  omega'),
232:('(lane start : Nat) (h : Emitted 8 lane) (caller : start = 0 ∨ start = 8)','lane < 8 ∧ start+lane < 16','have b := h.2\n  omega'),
233:('(length index : Nat) (shape : length ≤ 4) (h : Emitted length index)','index < length ∧ index < 4','have b := h.2\n  omega'),
237:('(limb pattern column : Nat) (hl : Emitted 16 limb) (hp : Emitted 14 pattern) (hc : column ∈ PV_B3Q_FrozenTables.columns)','limb < 16 ∧ pattern < 14 ∧ column < 16','exact ⟨hl.2,hp.2,PV_B3Q_FrozenTables.column_member_bound column hc⟩'),
240:('(block : Nat) (h : Emitted 64 block)','block < 64','exact h.2'),
310:('(group : Nat) (h : Emitted 4 group)','4*group < 16 ∧ 4*group+1 < 16 ∧ 4*group+2 < 16 ∧ 4*group+3 < 16 ∧ group < 4','have b := h.2\n  omega'),
326:('(lane limb : Nat) (hl : Emitted 16 lane) (hb : Emitted 4 limb)','lane < 16 ∧ limb < 4','exact ⟨hl.2,hb.2⟩'),
331:('(lane : Nat) (h : Emitted 16 lane)','lane < 16','exact h.2'),
355:('(mask : Aeneas.Std.U16) (h : mask ≠ 0#u16)','(Aeneas.Std.UScalar.cast .Usize (PV_B3Q_BitCounts.word (PV_B3Q_BitCounts.bits mask).ctz)).val < 16','exact PV_B3Q_PanicGuards.mask_read_bound mask h'),
430:('(output limb : Nat) (ho : Emitted 4 output) (hl : Emitted 4 limb)','output < 4 ∧ limb < 4 ∧ (output=0 ∨ output=1 ∨ output=2 ∨ output=3)','have o := ho.2\n  have l := hl.2\n  omega')}
manifest=[]
for r in x['functions']:
 fid=r['id'];rows=r['rows'];static=[(q['index'],q['array_length'])for q in rows if q['constant_checked']];dynamic=[q for q in rows if not q['constant_checked']]
 assert not dynamic or fid in C,('missing shape',fid)
 m=f'PV_B3Q_IndexGuard{fid}';s='import PV_B3Q_LoopGuards\nimport PV_B3Q_TableGuards\nnamespace '+m+'\nopen Aeneas Aeneas.Std PV_B3Q_LoopGuards\nset_option autoImplicit false\n'
 if static:
  s+='def constantReads : List (Nat × Nat) := ['+','.join(f'({a},{b})'for a,b in static)+']\n'
  s+='theorem constant_bounds : constantReads.all (fun p => decide (p.1 < p.2)) = true := by decide\n#print axioms constant_bounds\n'
 if dynamic:
  args,prop,proof=C[fid];s+=f'theorem dynamic_bounds {args} :\n {prop} := by\n  {proof}\n#print axioms dynamic_bounds\n'
 s+='end '+m+'\n';p=O/(m+'.lean');p.write_text(s)
 manifest.append(dict(module=m,source_function=r['name'],function_id=fid,source_span=r['span'],source_text_sha256=hashlib.sha256((r['source']or'').encode()).hexdigest(),index_sites=len(rows),static_sites=len(static),dynamic_sites=len(dynamic),source_sha256=hashlib.sha256(p.read_bytes()).hexdigest(),status='arithmetic prerequisite only; caller/event/source association not certified by generator',additional_limits=('high expand caller only; low caller theorem in PV_B3Q_ExpandGuards'if fid==185 else '')))
(D/'function-guard-manifest.json').write_text(json.dumps(manifest,indent=2)+'\n')
print(len(manifest),'function modules,',sum(r['index_sites']for r in manifest),'sites')
