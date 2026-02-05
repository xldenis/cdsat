#[cfg(creusot)]
macro_rules! Snapshot {
    ($t:ty) => {creusot_contracts::prelude::Snapshot<$t>}
}

#[cfg(not(creusot))]
macro_rules! Snapshot {
    ($t:ty) => {creusot_contracts::prelude::Snapshot<()>}
}

pub(crate) use Snapshot;
