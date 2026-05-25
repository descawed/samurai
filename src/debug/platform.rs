use std::time::{Duration, Instant};

use sysinfo::{Pid, Process, ProcessesToUpdate, ProcessRefreshKind, RefreshKind, System, UpdateKind};

#[derive(Debug)]
pub struct Platform {
    system: System,
    last_refresh: Instant,
    refresh_interval: Duration,
}

impl Platform {
    fn process_refresh_kind() -> ProcessRefreshKind {
        ProcessRefreshKind::nothing().with_exe(UpdateKind::OnlyIfNotSet)
    }

    fn refresh_kind() -> RefreshKind {
        RefreshKind::nothing().with_processes(Self::process_refresh_kind())
    }

    pub fn new(refresh_interval: Duration) -> Self {
        let system = System::new_with_specifics(Self::refresh_kind());
        Self {
            system,
            last_refresh: Instant::now(),
            refresh_interval,
        }
    }

    pub fn refresh(&mut self) {
        self.system.refresh_processes_specifics(
            ProcessesToUpdate::All,
            true,
            Self::process_refresh_kind(),
        );
        self.last_refresh = Instant::now();
    }

    pub fn refresh_if_stale(&mut self) {
        if (Instant::now() - self.last_refresh) >= self.refresh_interval {
            self.refresh();
        }
    }

    pub fn is_pid_alive(&self, pid: Pid) -> bool {
        self.system.process(pid).is_some_and(Process::exists)
    }

    pub fn active_processes(&self) -> impl Iterator<Item = (Pid, &Process)> {
        self.system.processes().iter().map(|(pid, process)| (*pid, process))
    }
}