from pathlib import Path
E=Path(__file__).resolve().parent
s=(E/'NBW_harness.patch').read_text()
for target,output in [('NBW_native.rs','NBW_native.rs.txt'),('KMX_stubs.rs','NBW_KMX_stubs.rs.txt')]:
 part=s.split('+++ b/crates/aspis-r1-cost-probe/src/'+target+'\n',1)[1].split('--- ',1)[0]
 (E/output).write_text(''.join(line[1:] for line in part.splitlines(keepends=True) if line.startswith('+')))
