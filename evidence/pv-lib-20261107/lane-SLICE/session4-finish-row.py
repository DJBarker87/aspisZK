import sys,json,pathlib,subprocess
E=pathlib.Path('evidence/pv-lib-20261107/lane-SLICE')
row=sys.argv[1];a=int(sys.argv[2]);detail=sys.argv[3]
r=json.loads((E/f'receipt-{a}.json').read_text());assert r['accepted'] and r['target']=='PV_LIB_SLICE_Spec_'+row
text=f'''# {row}: frozen statement comparison (session 4)

Module: lean/PV_LIB_SLICE_Spec_{row}.lean; focused attempt {a}.
Pre, Post, MachineSpec and Contract : Prop are elaborated; Contract is unproved.
Source/provider cohort is STX 3eb0cb97b63aaf110327a99529cbbca93c670dca;
frozen prose is lane SPEC a84dc05c68e, PSPEC_COMMON revision 2 / SPEC-C2.

{detail}

Common package comparison: first own completion/fault/actual consumed pending
is used, never execution into lower caller code. Pending requires no completed
frame and no resolved BODY. Infinite behavior retains every observable finite
prefix. Exact full Result payloads, world and ordered events are fixed by the
named source execution. Abort observes only events. Lower and suspended
continuations and all pre-existing source/heap data outside the actual mutable
argument roots and fresh allocation intervals are framed. Entry carries typed
initialized non-null aligned bounded references, registered ownership and live
numbering. No future read, decoder success or successful child premise occurs.
Activation counters are abstracted in observation, never equated across calls.

MachineSpec is over an arbitrary machine and reuses the existing named
OWNER/copy/set_len carrier, program table, handler and zero-cast interpretation;
allocation and reservation channels are explicit. It does not assume this
Post or a child Contract. Named primitive adequacy/bindings, D877 summary graph
transport and frame preservation are later proof obligations. Their absence
is not a missing statement. All allocating transitive bodies, null/layout and
abort branches remain in the source reference, rather than a blanket abort.
Nothing here closes a ledger row or supplies an endpoint premise.
'''
(E/f'SESSION4_{row}_COMPARISON.md').write_text(text)
p=E/'SESSION4_CONTRACT_INDEX.json';idx=json.loads(p.read_text()) if p.exists() else {'order':['f21','f13','f6','f5','f8','f7','f9','f4','f2','f1','f0'],'statements':{'f21':49924},'contract_instances':0,'joint_witness':None}
idx['statements'][row]=a;p.write_text(json.dumps(idx,indent=2)+'\n')
h=E/'HANDOFF.md';old=h.read_text();marker='# Session 4 checkpoint\n';
if marker in old:old=old[old.index('\n--- historical ---\n')+len('\n--- historical ---\n'):]
h.write_text(marker+f"\nCompiled whole statements: {', '.join(idx['statements'])}.\nContract instances: 0 (statements only). Latest {row}/{a}; comparison\nSESSION4_{row}_COMPARISON.md. Exact receipts retain caps, turns, revisions,\nRSS, wall, swap and axioms. Next work follows SESSION4_CONTRACT_INDEX.json.\nNo raw audit yet this session; next raw49693, new roots once at end.\n\n--- historical ---\n"+old)
subprocess.run(['git','add','--sparse','lean/PV_LIB_SLICE_Spec_'+row+'.lean',str(E)],check=True)
subprocess.run(['git','commit','-m','State '+row+' contract and record package comparison'],check=True)
