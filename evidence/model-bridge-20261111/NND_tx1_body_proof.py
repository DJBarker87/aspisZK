from pathlib import Path
E=Path(__file__).resolve().parent;p=E/'NND_Stage1Eval.lean';s=p.read_text();a=s.index(' unfold body bodyValue');b=s.index('\n#print axioms',a)
steps=[('seq','NND_Returned.ofExcept env _'),('seq','NND_Returned.ofExcept env _'),('seq','NND_Returned.ofExcept env _'),('seq','NND_Returned.ofExcept env _'),('bind','NND_Returned.ofExcept env _','checkpointData'),('seq','NND_Returned.ofExcept env _'),('bind','NND_Returned.ofExcept env _','publicData'),('bind','NND_Returned.ofOption env _ _','st'),('seq','NND_Returned.rs_lift _ env () (NND_Returned.alloc env)'),('seq','NND_Returned.check env _ _'),('bind','NND_Returned.ofOption env _ _','candidate'),('bind','NND_Returned.ofExcept env _','proofData'),('seq','NND_Returned.check env _ _'),('bind','NND_Returned.call _ _ _ env _ (NND_Tx1ReturnedValues.first_returned V P F _ env)','checkpoint'),('seq','NND_Returned.check env _ _')]
proof=' unfold body bodyValue\n';indent=' '
for item in steps:
 kind,expr,*arg=item
 proof+=indent+'apply NND_Returned.'+('rs_bind' if kind=='bind' else 'seq')+'\n'+indent+'· exact '+expr+'\n'+indent+'· '
 if kind=='bind':proof+='intro '+arg[0]+'\n'
 else:proof+='\n'
 indent+='  '
proof+=indent+'exact NND_Returned.rs_pure env _\n'
s=s[:a]+proof+s[b:];p.write_text(s)
