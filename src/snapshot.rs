#[cfg(creusot)]
macro_rules! Snapshot {
    ($t:ty) => {creusot_std::prelude::Snapshot<$t>}
}

#[cfg(not(creusot))]
macro_rules! Snapshot {
    ($t:ty) => {creusot_std::prelude::Snapshot<()>}
}

pub(crate) use Snapshot;
