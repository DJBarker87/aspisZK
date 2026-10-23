from pathlib import Path
H=Path('/home/dombarker/project-offloads/s126-real-sdk-20261021')
p=H/'crate/Cargo.toml'
s=p.read_text().replace('/Users/dominic/ZK/.worktrees/s126-caller-20261021','/home/dombarker/project-offloads/codex-cx-repin-s6-20261020/src')
p.write_text(s)
p=H/'kit/capped.py';s=p.read_text().replace('/home/dombarker/project-offloads/codex-cx-repin-s6-20261020','/home/dombarker/project-offloads/s126-real-sdk-20261021');p.write_text(s)
(H/'source-revision.txt').write_text('d8fc9db732c70ef8dd1dd548184326318d5e1ad1\n')
