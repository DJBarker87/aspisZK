#[derive(Default)]
pub(super) struct LiftGate {
    result: std::sync::Mutex<Option<bool>>,
    ready: std::sync::Condvar,
}
impl LiftGate {
    pub(super) fn publish(&self, ok: bool) {
        *self.result.lock().unwrap() = Some(ok);
        self.ready.notify_all();
    }
    pub(super) fn wait(&self) -> bool {
        let mut result = self.result.lock().unwrap();
        while result.is_none() { result = self.ready.wait(result).unwrap(); }
        result.unwrap()
    }
}
// Wake waiting families even if the first lift panics. The original panic is
// still joined/resumed by ordered_families and normalized to rejection.
pub(super) struct LiftGateGuard<'a>(pub(super) &'a LiftGate);
impl Drop for LiftGateGuard<'_> {
    fn drop(&mut self) {
        let mut result = self.0.result.lock().unwrap();
        if result.is_none() { *result = Some(false); self.0.ready.notify_all(); }
    }
}
