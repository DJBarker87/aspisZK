//! Linux test observer of actual ledger create/close events, including retries.
use std::{fs::File,io::Read,os::{fd::FromRawFd,unix::ffi::OsStrExt},path::Path,ffi::CString};
unsafe extern "C" {
    fn inotify_init1(flags:i32)->i32;
    fn inotify_add_watch(fd:i32,path:*const std::ffi::c_char,mask:u32)->i32;
}
pub struct LedgerWatch { file:File }
impl LedgerWatch {
    pub fn new(path:&Path)->Self {
        let name=CString::new(path.as_os_str().as_bytes()).unwrap();
        // O_NONBLOCK | O_CLOEXEC. Each unique retained file creates at most two
        // queued records, so no unbounded watcher thread or timing data enters.
        let fd=unsafe {inotify_init1(0x800|0x80000)};
        assert!(fd>=0,"{}",std::io::Error::last_os_error());
        let file=unsafe {File::from_raw_fd(fd)};
        assert!(unsafe {inotify_add_watch(fd,name.as_ptr(),0x100|0x8)}>=0);
        Self{file}
    }
    pub fn drain(&mut self)->Vec<(u32,String)> {
        let mut out=Vec::new();let mut bytes=[0u8;4096];
        loop {
            let n=match self.file.read(&mut bytes) {
                Ok(n)=>n,
                Err(e) if e.kind()==std::io::ErrorKind::WouldBlock=>break,
                Err(e) if e.kind()==std::io::ErrorKind::Interrupted=>continue,
                Err(e)=>panic!("ledger watch: {e}"),
            };
            assert!(n>0);let mut at=0;
            while at<n {
                assert!(at+16<=n);
                let mask=u32::from_ne_bytes(bytes[at+4..at+8].try_into().unwrap());
                let len=u32::from_ne_bytes(bytes[at+12..at+16].try_into().unwrap()) as usize;
                assert_eq!(mask&0x4000,0,"inotify queue overflow");
                assert!(at+16+len<=n);
                let name=&bytes[at+16..at+16+len];
                let end=name.iter().position(|b|*b==0).unwrap_or(name.len());
                out.push((mask,std::str::from_utf8(&name[..end]).unwrap().to_owned()));
                at+=16+len;
            }
        }
        out
    }
}
