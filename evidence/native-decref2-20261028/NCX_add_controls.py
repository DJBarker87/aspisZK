from pathlib import Path
p=Path('evidence/native-decref2-20261028/NCX_instrument.py');s=p.read_text()
needle=" d['crates/aspis-statement/src/NCX_native.rs']=n"
s=s.replace(needle,''' for name in ['VerifierRegistryV2','VerifierRegistryEntryV2']:
  fs=fields[name]
  values=','.join(f+(': match kani::any::<u8>()%4{0=>VerifierEntryStatusV1::Pending,1=>VerifierEntryStatusV1::Active,2=>VerifierEntryStatusV1::Paused,_=>VerifierEntryStatusV1::Retired}' if f=='status' else ':kani::any()') for f in fs)
  n+=f'impl kani::Arbitrary for {name}{{fn any()->Self{{Self{{{values}}}}}}\\n'
 n+='impl kani::Arbitrary for PoolV1VerifierRegistryFormatError {fn any()->Self{match kani::any::<u8>()%12{'+','.join(str(i)+'=>Self::'+v for i,v in enumerate(['WrongLength','WrongMagic','WrongVersion','NonZeroReserved','UnsupportedFlags','InvalidStatus','InvalidAuthorityMode','ZeroRequiredBinding','InvalidActivationDelay','InvalidStatementVersion','InvalidRetirementSlot']))+',_=>Self::InvalidDeploymentMode}}}\\n'
''' +needle)
needle=" d['programs/r1-cost-probe/src/NCX_native.rs']=n"
s=s.replace(needle,''' shape=os.environ.get('NCX_SHAPE','registry')
 ty='VerifierRegistryV2' if shape=='registry' else 'VerifierRegistryEntryV2'
 flag='bump' # common scalar, unmodified but weaker than complete record
 other='programdata_bump'
 control=os.environ.get('NCX_CONTROL','positive')
 prop='matches!(r,Ok(v) if v.bump==a.bump)'
 if control=='ensures':prop='!('+prop+')'
 n+=f'#[kani::modifies(x)]\\n#[kani::ensures(|r:&Result<{ty},PoolV1VerifierRegistryFormatError>|{prop})]\\nfn NCX_shape(a:{ty},x:&mut u8,y:&mut u8)->Result<{ty},PoolV1VerifierRegistryFormatError>{{*x=1;'+('*y=2;' if control=='modifies' else '')+'Ok(a)}\\n'
 n+='#[kani::proof_for_contract(NCX_shape)]\\n'+attrs+'#[kani::unwind(34)]\\nfn NCX_shape_contract(){let a=kani::any();let mut x=kani::any();let mut y=kani::any();let _=NCX_shape(a,&mut x,&mut y);}\\n'
 n+='#[kani::proof]\\n'+attrs+'#[kani::unwind(34)]\\nfn NCX_shape_real(){let a:'+ty+'=kani::any();let before=a.programdata_bump;let mut x=kani::any();let mut y=kani::any();let r=NCX_shape(a,&mut x,&mut y);assert!(matches!(r,Ok(v) if v.programdata_bump==before));}\\n'
 n+='#[kani::proof]\\n#[kani::stub_verified(NCX_shape)]\\n'+attrs+'#[kani::unwind(34)]\\nfn NCX_shape_stub(){let a:'+ty+'=kani::any();let before=a.programdata_bump;let mut x=kani::any();let mut y=kani::any();let r=NCX_shape(a,&mut x,&mut y);assert!(matches!(r,Ok(v) if v.programdata_bump==before));}\\n'
''' +needle)
p.write_text(s)
