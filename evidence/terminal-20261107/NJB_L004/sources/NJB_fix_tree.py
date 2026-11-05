from pathlib import Path
b=Path(__file__).resolve().parent;p=b/'NJB_src/tools/r1-builder-reference/tree.rs';p.parent.mkdir(parents=True,exist_ok=True);p.write_bytes((b/'NJB_tree.rs.txt').read_bytes());print('frozen external path restored')
