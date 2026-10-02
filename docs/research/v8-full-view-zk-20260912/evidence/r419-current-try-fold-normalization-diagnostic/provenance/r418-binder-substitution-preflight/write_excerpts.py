from pathlib import Path
import hashlib
HERE=Path(__file__).resolve().parent
files={
 'Charon ast/types_utils.rs':(HERE/'pinned-charon/charon/src/ast/types_utils.rs',[(1064,1161),(1233,1277)]),
 'Charon ast/gast_utils.rs':(HERE/'pinned-charon/charon/src/ast/gast_utils.rs',[(100,126)]),
 'Charon ast/gast.rs':(HERE/'pinned-charon/charon/src/ast/gast.rs',[(214,250),(422,462)]),
 'Charon ast/expressions.rs':(HERE/'pinned-charon/charon/src/ast/expressions.rs',[(516,555)]),
 'Charon hide_allocator_param.rs':(HERE/'pinned-charon/charon/src/transform/simplify_output/hide_allocator_param.rs',[(1,85)]),
 'Charon expand_associated_types.rs':(HERE/'pinned-charon/charon/src/transform/normalize/expand_associated_types.rs',[(571,660),(1040,1135),(1315,1345),(1410,1465)]),
 'Aeneas SymbolicToPureTypes.ml':(HERE/'pinned-aeneas/src/symbolic/SymbolicToPureTypes.ml',[(246,270),(1037,1088),(1122,1155)]),
 'Aeneas Substitute.ml':(HERE/'pinned-aeneas/src/llbc/Substitute.ml',[(20,85)]),
}
out=[]
for title,(path,ranges) in files.items():
 lines=path.read_text().splitlines()
 out += [f'## {title}',f'Full source SHA256: {hashlib.sha256(path.read_bytes()).hexdigest()}','']
 for a,b in ranges:
  out.append(f'### Lines {a}-{b}')
  out.extend(f'{i}: {lines[i-1]}' for i in range(a,min(b,len(lines))+1))
  out.append('')
(HERE/'source-excerpts.txt').write_text('\n'.join(out)+'\n')
