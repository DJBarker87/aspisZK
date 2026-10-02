#!/usr/bin/env python3
"""Write exact numbered excerpts from the copied pinned source and receipts."""
import pathlib
ROOT=pathlib.Path(__file__).resolve().parent
src=ROOT/'pinned-r289-source'
blocks=[
 ('Pinned R289 PrePasses.ml: direct and raw pointer metadata recognition/rewrite (lines 128-210)',src/'PrePasses.ml',128,210),
 ('Pinned R289 PrePasses.ml: raw metadata read classifier (lines 260-278)',src/'PrePasses.ml',260,278),
 ('Pinned R289 PrePasses.ml: pass fallbacks (lines 383-388)',src/'PrePasses.ml',383,388),
 ('Pinned R289 PrePasses.ml: pass registration (lines 3534-3554)',src/'PrePasses.ml',3534,3554),
 ('Pinned R289 SymbolicToPureValues.ml: mprojection PtrMetadata handling (lines 662-670)',src/'symbolic/SymbolicToPureValues.ml',662,670),
 ('Pinned R289 InterpMatchCtxs.ml: TPtrMetadata type matching (lines 418-423)',src/'interp/InterpMatchCtxs.ml',418,423),
 ('Pinned R289 Builtin.ml: Slice.len builtin signature (lines 194-206)',src/'llbc/Builtin.ml',194,206),
 ('Pinned R289 ExtractBuiltinLean.ml: Rust path to Lean Slice.len mapping (lines 1102-1104)',src/'extract/ExtractBuiltinLean.ml',1102,1104),
 ('Pinned R289 InterpPaths.ml: generic inconsistent projection failure (lines 231-237)',src/'interp/InterpPaths.ml',231,237),
 ('Aeneas standard Slice.lean: Slice.len Lean implementation (lines 49-55)',ROOT/'Slice.lean',49,55),
]
out=[]
for title,p,a,b in blocks:
 lines=p.read_text().splitlines()
 out.append('\n### '+title+'\n')
 out.extend(f'{i:5d} {lines[i-1]}' for i in range(a,min(b,len(lines))+1))
log=(ROOT.parent/'r300-slice-last-translation/translate.log').read_text().splitlines()
needles=['Imported:','Inconsistent projection:','- pe:','(Values.VBorrow','(Generated_Types.TRef','Source:','Compiler source:','Command exited with non-zero status','Elapsed (wall clock) time','Maximum resident set size','Swaps:','Exit status:']
selected=[]
for i,line in enumerate(log):
 if any(n in line for n in needles): selected.append(f'{i+1:5d} {line}')
out.append('\n### R300 translation failure log exact selected lines\n')
out.extend(selected)
(ROOT/'source-excerpts.txt').write_text('\n'.join(out)+'\n')
