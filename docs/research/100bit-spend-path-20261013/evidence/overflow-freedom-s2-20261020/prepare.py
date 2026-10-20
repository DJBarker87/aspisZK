from pathlib import Path
import re,json,hashlib
root=Path(__file__).resolve().parents[2]
src=root/'evidence/stage2-continuation-20261020/generated/AspisR1Stage2/Funs.lean'
s=src.read_text(); lines=s.splitlines()
# Complete definitions, retaining original bodies exactly, without generated options.
starts=list(re.finditer(r'^def\s+([\w.]+)',s,re.M))
selected=['compact.FINAL_LEN','compact.HEADER','compact.OFF_SEMANTIC','compact.SEMANTIC_COMPACT_VALUES','verifier.SEMANTIC_BYTES','compact.LOGICAL_SEMANTIC','compact.COMPACT_SEMANTIC','compact.OFF_Y1','compact.COMPACT_Y1','compact.OFF_INACTIVE','compact.OFF_ROUND0','compact.OFF_FOLDED_ROOT','compact.OFF_ROUND1','compact.OFF_FINAL','compact.OFF_OPENINGS','compact.OPENING','compact.QUERIES','compact.OFF_NODES','compact.MAX_NODES','compact.FIXED','compact.MAX_PROOF','compact.PROOF_BYTES','verifier.candidate.opening','multiproof.index_at','multiproof.value_at','multiproof.Arity.bits','multiproof.LEAF_BITS','multiproof.Arity.levels','multiproof.Arity.width','verifier.Reader.raw','verifier.CHECKPOINT_FIXED']
# Include defs whose attributes and def share a line.
starts=list(re.finditer(r'^(?:@\[[^\n]*\]\s*)?def\s+([\w.]+)',s,re.M))
pieces=[]; pins=[]
for m in starts:
 if m[1] not in selected: continue
 # body ends at next doc comment (all selected declarations have one following).
 end=s.find('\n/--',m.end())
 body=s[m.start():end].rstrip()
 # attrs on preceding lines unnecessary; same-line irreducible replaced with def for copied leaf.
 body=re.sub(r'^@\[[^\n]*\]\s*','',body)
 pieces.append(body)
 pins.append({'name':m[1],'line':s[:m.start()].count('\n')+1,'body_sha256':hashlib.sha256(body.encode()).hexdigest()})
assert len(pieces)==len(selected),(len(pieces),set(selected)-{p['name'] for p in pins})
out=root/'lean/R22Stage2LocalBodies.lean'
out.write_text('import Stage2ContinuationTypes\nopen Aeneas Aeneas.Std Result ControlFlow Error\nset_option autoImplicit false\n/-! Verbatim emitted leaf bodies, without generator attributes/options.\nSource locations and body hashes: overflow-freedom-s2 packet/body-pins.json.\nThis module does not import the unavailable FunsExternal backend. -/\nnamespace AspisR1Stage2\n\n'+'\n\n'.join(pieces)+'\n\nend AspisR1Stage2\n')
(root/'evidence/overflow-freedom-s2-20261020/body-pins.json').write_text(json.dumps({'source':str(src.relative_to(root)),'sha256':hashlib.sha256(src.read_bytes()).hexdigest(),'declarations':pins},indent=2)+'\n')
# Lexical per-definition census: all scalar operators, casts, checked/wrapping calls,
# collection accesses and calls crossing the emitted body boundary.
patterns={'add':r' \+ ','sub':r' - ','mul':r' \* ','div':r' / ','rem':r' % ','shift_left':r'<<<','shift_right':r'>>>','cast':r'UScalar.cast','index':r'Array.index_usize|Array.update|Slice.index_usize|Slice.index|Vec.index|index_mut','safe_get':r'core.slice.Slice.get','copy_slice':r'copy_from_slice','explicit_checked':r'checked_\w+','explicit_wrapping':r'wrapping_\w+'}
rows=[]; current='preamble'
for no,line in enumerate(lines,1):
 if re.match(r'^(?:@\[[^\n]*\]\s*)?def\b',line):
  tail=' '.join(lines[no-1:no+3]); m=re.search(r'\bdef\s+([\w.]+)',tail)
  current=m[1] if m else 'unknown'
 kinds=[k for k,p in patterns.items() if re.search(p,line)]
 if kinds: rows.append({'function':current,'line':no,'kinds':kinds,'text':line.strip()})
(root/'evidence/overflow-freedom-s2-20261020/operation-census.json').write_text(json.dumps({'source':str(src.relative_to(root)),'sha256':hashlib.sha256(src.read_bytes()).hexdigest(),'warning':'Lexical site inventory; multiline library calls require manual review; not a verified call graph.','sites':rows},indent=2)+'\n')
