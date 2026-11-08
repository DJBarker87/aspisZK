"""Retain symlink staging records and hardlink immutable own sources for Lean -R.
No deletion, no byte copy, and no mutation of the original sources.
"""
import pathlib,os
V=pathlib.Path('/home/dombarker/project-offloads/codex-pv-lib-slice-20261107/v1-coherence');S=V/'sources-canonical';A=S/'symlink-staging';A.mkdir(exist_ok=True);n=0
for p in S.glob('*.lean'):
 if not p.is_symlink():continue
 target=p.resolve();p.rename(A/p.name);os.link(target,p);n+=1
print('Retained and replaced',n,'source symlinks with immutable own hardlinks')
