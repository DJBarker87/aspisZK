from pathlib import Path
import subprocess,sys,json
E=Path(__file__).resolve().parent
cases=['InvalidArgument','InvalidInstructionData','InvalidAccountData','AccountDataTooSmall','InsufficientFunds','IncorrectProgramId','MissingRequiredSignature','AccountAlreadyInitialized','UninitializedAccount','NotEnoughAccountKeys','AccountBorrowFailed','MaxSeedLengthExceeded','InvalidSeeds','BorshIoError','AccountNotRentExempt','UnsupportedSysvar','IllegalOwner','MaxAccountsDataAllocationsExceeded','InvalidRealloc','MaxInstructionTraceLengthExceeded','BuiltinProgramsMustConsumeComputeUnits','InvalidAccountOwner','ArithmeticOverflow','Immutable','IncorrectAuthority']
start=int(sys.argv[1]) if len(sys.argv)>1 else 63
offset=int(sys.argv[2]) if len(sys.argv)>2 else 0
for i,(case,mode) in enumerate(((c,m) for c in cases[offset:] for m in ['positive','error']),start):
 a=f'NGG_K{i:03d}'
 subprocess.run([sys.executable,str(E/'NGG_decode_cut.py'),mode,'reject','all',case],check=True)
 r=subprocess.run([sys.executable,str(E/'NGG_kani_run.py'),a,'pair_forest::NGG_DecodeCut::association'],capture_output=True,text=True)
 print(a,case,mode,r.returncode,r.stdout.strip(),flush=True)
 p=E/a/'stdout.log'
 if not p.exists():print('Controller/transport error recorded',flush=True);raise SystemExit(1)
 out=p.read_text()
 if 'CBMC timed out.' in out or (mode=='positive' and r.returncode!=0) or (mode!='positive' and 'VERIFICATION:- FAILED' not in out):
  print(json.dumps({'failed_checks':[l for l in out.splitlines() if l.startswith('Failed Checks:')]}),flush=True);raise SystemExit('STOP review; no unchanged timeout rerun')
