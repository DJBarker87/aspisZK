"""Port fresh split-reference emission; reuse only byte-equivalent prior bodies.
Raw emissions are immutable. Every numeric API port is recorded explicitly.
"""
from pathlib import Path
import re,json,hashlib
D=Path('evidence/pv-b3p6-20261028');R=D/'raw227-parts-resume5';O=D/'raw227-complete-resume5'
blocks=lambda s:re.split(r'(?=^/-- \[)',s,flags=re.M)
def name(b):
 m=re.search(r'^(?:def|structure|inductive)\s+(\S+)',b,re.M);return m[1]if m else None
def body(b):
 m=re.search(r'^(?:def|structure|inductive)\s+',b,re.M);assert m
 return re.sub(r'\s+',' ',re.sub(r'\nend PV_B3P_227\s*$','',b[m.start():])).strip()
for kind in ('Types','Funs'):
 old={name(b):b for b in blocks((O/(kind+'.lean')).read_text())if name(b)};new={name(b):b for b in blocks((R/(kind+'.lean')).read_text())if name(b)}
 if kind=='Types':assert old.keys()==new.keys();assert all(body(old[n])==body(new[n])for n in old);continue
 changed=[n for n in old if body(old[n])!=body(new[n])];added=[n for n in new if n not in old]
 assert set(changed)=={'reference_field.qm31_sum_products3_prepared','reference_poseidon.internal_linear_lazy'},changed
 assert len(added)==5,added
 prefix=[n for row in json.load(open(D/'split227-resume5.json'))['chunks'][:20]for n in row['definitions']]
 shared=['aspis_core.field.QM31.ZERO','reference_terminal.claim227','reference_terminal.select227_loop.body','reference_terminal.select227_loop','reference_terminal.select227']
 assert all(body(old[n])==body(new[n])for n in prefix+shared)
 remaining=[n for n in new if n not in prefix+shared];assert remaining[0]=='reference_field.accumulate_prepared227'
 header=blocks((R/'Funs.lean').read_text())[0].replace('import Aeneas\n','import Aeneas.Std\nimport Aeneas.Tactic.RustAttributes\n');header=re.sub(r'^import \S+\.Types$', 'import PV_B3P_E227_19',header,flags=re.M)
 source=header+''.join(new[n]for n in remaining)
 source=source.replace('@[global_simps, irreducible]','@[irreducible]')
 ports=[]
 # All signed shift literals are nonnegative; only these four are present.
 for value in ('4','10','20','31'):
  count=source.count(value+'#i32');source=source.replace(value+'#i32',value+'#u32')
  if count:ports.append(dict(kind='positive signed shift literal to U32',value=int(value),count=count))
 # U64 wrapping shifts with source usize counts: preserve low6 count bits.
 for count in ('level_index',):
  pattern=r'(Std\.U64\.wrapping_shr\s+\w+) '+count+r'\b';source,num=re.subn(pattern,r'\1 (UScalar.cast .U32 '+count+')',source);ports.append(dict(kind='usize count low6 preserving cast',expression=count,count=num))
 pattern=r'(Std\.U64\.wrapping_shr\s+(?:[\w.]+)\s+)(\d+)#usize'
 source,num=re.subn(pattern,r'\g<1>\2#u32',source);ports.append(dict(kind='small usize shift literals to U32',count=num))
 source,num=re.subn(r'(Std\.U64\.wrapping_shl \w+) shift\b',r'\1 (UScalar.cast .U32 shift)',source);ports.append(dict(kind='U8 count widening to U32',count=num,law='PV_B3P_Shift227.u8_u32_value'))
 assert num==4
 # Give literal Array.make lengths explicit cons-shape proofs, without unfolding data.
 positions=[]
 for m in re.finditer(r'Array\.make\s+\d+#usize\s+\[',source):
  depth=1;i=m.end()
  while depth:depth+=(source[i]=='[')-(source[i]==']');i+=1
  positions.append(i)
 for i in sorted(positions,reverse=True):source=source[:i]+' (by simp only [List.length_cons,List.length_nil]; rfl)'+source[i:]
 # Check-only partition; no data/operation edits beyond listed numeric API ports.
 bb=blocks(source);header=bb[0];decls={name(b):b for b in bb[1:]};assert list(decls)==remaining
 boundaries=['reference_field.accumulate_prepared227','reference_field.qm31_sum_products3_prepared','reference_poseidon.EXTERNAL_INITIAL','reference_poseidon.external_group227','reference_poseidon.external_local_packed','reference_poseidon.full_round','reference_poseidon.internal_round','reference_terminal.DOMAIN_OWNER_KEY','reference_terminal.lift_m31','reference_terminal.sum_interval227_loop.body','reference_terminal.add_digest_binding','reference_terminal.public_digest_lanes','reference_terminal.scalar_lanes','reference_terminal.composition_parts_loop0.body','reference_terminal.terminal_parts']
 cuts=[remaining.index(n)for n in boundaries]+[len(remaining)];assert cuts==sorted(cuts)
 rows=[];prev='PV_B3P_E227_19';check='--check'in __import__('sys').argv
 for j,(a,b)in enumerate(zip(cuts,cuts[1:])):
  mod=f'PV_B3P_P227_{j:02}';part=header.replace('import PV_B3P_E227_19','import '+prev)+''.join(decls[n]for n in remaining[a:b]);part=re.sub(r'\nend PV_B3P_227\s*$','',part)+'\nend PV_B3P_227\n\n'+''.join('#print axioms PV_B3P_227.'+n+'\n'for n in remaining[a:b]);p=D/'lean'/(mod+'.lean')
  if check:assert p.read_text()==part,p
  else:p.write_text(part)
  rows.append(dict(module=mod,names=remaining[a:b],source=str(p),sha256=hashlib.sha256(part.encode()).hexdigest(),imports=[prev]));prev=mod
 agg='import '+prev+'\n\n#print axioms PV_B3P_227.reference_terminal.reference227\n';p=D/'lean/PV_B3P_PartsEmission227.lean'
 if check:assert p.read_text()==agg
 else:p.write_text(agg)
 record=dict(raw_funs_sha256=hashlib.sha256((R/'Funs.lean').read_bytes()).hexdigest(),types_all_identical=True,changed_owned_bodies=changed,added_helpers=added,reused_body_identical_prefix=prefix,reused_focused_selection=shared,ports=ports,explicit_literal_size_proofs=len(positions),chunks=rows,raw_modified=False)
 if not check:(D/'port-parts227-resume5.json').write_text(json.dumps(record,indent=2)+'\n')
 print(json.dumps(dict(chunks=len(rows),remaining_definitions=len(remaining),changed=changed,added=added,ports=ports,checked=check)))
