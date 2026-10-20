#!/usr/bin/env python3
"""Prepare a test/extraction-only reference and a universal callback harness.
Never modifies the retained production tree. No verification claim is made
unless both Charon/Aeneas and the all-input Kani harness succeed.
"""
from pathlib import Path
import shutil
R=Path('/home/dombarker/project-offloads/codex-cx-prover-commit2-20261020')
P=R/'source-kani'
assert not P.exists()
shutil.copytree(R/'src',P)
parent=P/'crates/aspis-prover/src/state_only_hiding.rs'
original=(R/'source-builder/crates/aspis-prover/src/state_only_hiding.rs').read_text()
def function(name):
 start=original.index('fn '+name+'(')
 # Include generic-free fn definitions used by the isolated carried candidate.
 brace=original.index('{',start);level=1;end=brace+1
 while level:
  level+=(original[end]=='{')-(original[end]=='}');end+=1
 return original[start:end]
names=['build_mask_material_for_layout','append_qm31_mask_cell','write_qm31_padding_cell','append_m31_mask_cell','sample_m31_mask_cells','sample_mask_only_column']
s='use super::*;\n\n'+'\n\n'.join(function(n) for n in names)
s=s.replace('fn build_mask_material_for_layout(', 'pub(super) fn reference_build_mask_material_for_layout(')
s=s.replace('balance_m31_copy_inactive(', 'reference_balance_m31(').replace('balance_qm31_copy_inactive(', 'reference_balance_qm31(').replace('first_inactive_row(active)','reference_first_inactive(active)')
s+='''
fn reference_first_inactive(active: &[bool;1024]) -> usize {
    let mut row=0;
    while row<1024 {
        if !active[row] { return row; }
        row+=1;
    }
    panic!("generated layout has an inactive row")
}
fn reference_balance_m31(table: &mut [M31], dependent: usize, active: &[bool;1024]) -> Result<(),StateOnlyMaskBuildError> {
    if table.len()!=1024 || active[dependent] {return Err(StateOnlyMaskBuildError::TraceShape);}
    let mut sum=M31::ZERO;
    for row in 0..1024 {
        if !active[row] && row!=dependent {sum=sum.add(table[row]);}
    }
    table[dependent]=M31::ZERO.sub(sum);
    Ok(())
}
fn reference_balance_qm31(table: &mut [QM31], dependent: usize, active: &[bool;1024]) -> Result<(),StateOnlyMaskBuildError> {
    if table.len()!=1024 || active[dependent] {return Err(StateOnlyMaskBuildError::TraceShape);}
    let mut sum=QM31::ZERO;
    for row in 0..1024 {
        if !active[row] && row!=dependent {sum=sum.add(table[row]);}
    }
    table[dependent]=QM31::ZERO.sub(sum);
    Ok(())
}
#[cfg(kani)]
mod proofs {
    use super::*;
    struct Store(bool);
    impl StateOnlyMaskNonceStore for Store {
        fn reserve(&mut self, _: [u8;32], _: [u8;32])->bool {self.0}
    }
    #[kani::proof]
    fn shipped_vs_reference_fixed_sizes() {
        let hash: HashFn=kani::any();
        let binding: [u8;32]=kani::any();
        let entropy: [u8;32]=kani::any();
        let context=StateOnlyHidingContext {
            statement_digest:kani::any(),mask_nonce:kani::any(),
            mask_layout_fingerprint:kani::any(),layout_factor_fingerprint:kani::any(),
        };
        let active: [bool;1024]=kani::any();
        kani::assume(active.iter().any(|b| !*b));
        let cells: Vec<aspis_statement::TraceCell>=(0..3803).map(|i|aspis_statement::TraceCell{row:(i%1024) as u16,column:(i/1024) as u8}).collect();
        let reservation: bool=kani::any();
        let left=super::super::build_mask_material_for_layout(hash,binding,context,&entropy,&mut Store(reservation),&cells,&active);
        let right=reference_build_mask_material_for_layout(hash,binding,context,&entropy,&mut Store(reservation),&cells,&active);
        match (left,right) {
            (Ok(l),Ok(r))=>{
                assert_eq!(l.c1,r.c1);assert_eq!(l.mask_only_c1,r.mask_only_c1);
                assert_eq!(l.g,r.g);assert_eq!(l.h1_padding,r.h1_padding);
                assert_eq!(l.mask_nonce,r.mask_nonce);
            },
            (Err(l),Err(r))=>assert_eq!(l,r),
            _=>assert!(false),
        }
    }
}
'''
(parent.parent/'prover_commit_reference.rs').write_text(s)
parent.write_text(parent.read_text()+'\n#[cfg(any(kani,feature="prover-commit-reference"))]\n#[path="prover_commit_reference.rs"]\nmod prover_commit_reference;\n')
cargo=P/'crates/aspis-prover/Cargo.toml'
cargo.write_text(cargo.read_text().replace('[features]','[features]\nprover-commit-reference = []'))
