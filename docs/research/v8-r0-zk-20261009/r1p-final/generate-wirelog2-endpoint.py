#!/usr/bin/env python3
"""Generate the endpoint from the accounting signature by explicit specialization.
The captured signature diff must contain deletions only after specialization.
"""
from pathlib import Path
import difflib
root=Path(__file__).resolve().parents[1]
s=(root/'lean/R1Z/PrivacyR1HeadlineAcct.lean').read_text()
s=s.replace('import R1Z.PrivacyR1AcctModel','import R1Z.PhaseWireLog2Bin').replace('PrivacyR1HeadlineAcct','PrivacyR1HeadlineWire2')
a=s.index('    (log : '); b=s.index('local notation "base"',a)
s=s[:a]+ '\nlocal notation "log" => PhaseWireLog2Bin.log\n'+s[b:]
s=s.replace('variable (h : HonestProver K)', 'variable (input : HonestProver K)')
s=s.replace('    (x : Statement K CommitHandle)\n','    (x : Statement K CommitHandle)\nlocal notation "h" => PhaseWireLog2Bin.honest input\n',1)
a=s.index('    (fib : '); b=s.index('local notation "seed"',a)
s=s[:a]+'\nlocal notation "fib" => PhaseWireLog2Bin.fib\nlocal notation "opens" => PhaseWireLog2Bin.opens\n'+s[b:]
s=s.replace('privacy_headline_acct','privacy_headline_wire2')
s=s.replace('h.Instance', '(R0Z.ZkStatement.HonestProver.Instance h)').replace('h.public w', '(R0Z.ZkStatement.HonestProver.public h w)')
a=s.index('theorem privacy_headline_wire2'); b=s.index(' := by',a)
before=s[a:b]
a=s.index('    (R_wire_D80_batches'); b=s.index('    (observer_program',a)
s=s[:a]+s[b:]
a=s.index('theorem privacy_headline_wire2'); b=s.index(' := by',a)
after=s[a:b]
diff=list(difflib.unified_diff(before.splitlines(),after.splitlines(),fromfile='specialised-before',tofile='after',lineterm=''))
assert not any(line.startswith('+') and not line.startswith('+++') for line in diff)
a=s.index(' := by',a); b=s.index('\n#print axioms eight_pos',a)
s=s[:a]+''' := by
  exact PrivacyR1HeadlineAcct.privacy_headline_acct template log h outputs x decode fib opens
    builder_premises cF R_commit_quotient_fibres R_commit_exhaustion
    (PhaseWireLog2Bin.batches input outputs x template decode)
    (PhaseWireLog2Bin.ordered_log input outputs x template decode)
    observer_program R_wire_builder_checker_D75_retry G_sim_R_wire
'''+s[b:]
# Compile the verbatim specialised predecessor signature as well, in a namespace.
before_body = """ := by
  exact PrivacyR1HeadlineAcct.privacy_headline_acct template log h outputs x decode fib opens
    builder_premises cF R_commit_quotient_fibres R_commit_exhaustion
    R_wire_D80_batches R_wire_D80_ordered_log
    observer_program R_wire_builder_checker_D75_retry G_sim_R_wire
"""
i = s.index('theorem privacy_headline_wire2')
s = s[:i] + 'namespace Before\n' + before + before_body + 'end Before\n\n' + s[i:]
s = s.replace('#print axioms privacy_headline_wire2', '#print axioms Before.privacy_headline_wire2\n#print axioms privacy_headline_wire2')
s=s.replace('/-! Accounting-specialized headline. All decoder/execution joins are retained.\nThe source experiment here is the constructed finite binary-ROM experiment. -/', '''/-! D108 headline over the fixed S2 logical wire encoding. The only deleted
premises are the two D80 wire premises; decoder/execution joins remain. -/''')
(root/'lean/R1Z/PrivacyR1HeadlineWire2.lean').write_text(s)
# Keep verbatim signatures with common specialization context in the requested report.
report=root/'r1p-final/WIRELOG-20261021.md'
t=report.read_text()
audit_marker='\n## Frozen extension audit\n'
audit_tail=t[t.index(audit_marker):] if audit_marker in t else ''
marker='\n## Verbatim specialised before/after (D108)\n'
if marker in t: t=t[:t.index(marker)]
preamble=s[s.index('variable {CommitHandle'):s.index('namespace Before')]
t+=marker+'\nThe shared specialisation context is exactly:\n\n```lean\n'+preamble+'```\n\nBefore (the accounting headline after this specialisation):\n\n```lean\n'+before+'\n```\n\nAfter (the new endpoint signature):\n\n```lean\n'+after+'\n```\n\nMechanical signature diff (deletions only):\n\n```diff\n'+'\n'.join(diff)+'\n```\n'
report.write_text(t+audit_tail)
