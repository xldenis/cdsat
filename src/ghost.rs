#[cfg(creusot)]
macro_rules! Ghost {
    ($t:ty) => {creusot_contracts::prelude::Ghost<$t>}
}

#[cfg(not(creusot))]
macro_rules! Ghost {
    ($t:ty) => {creusot_contracts::prelude::Ghost<()>}
}

pub(crate) use Ghost;
