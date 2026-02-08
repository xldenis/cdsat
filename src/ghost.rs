#[cfg(creusot)]
macro_rules! Ghost {
    ($t:ty) => {creusot_std::prelude::Ghost<$t>}
}

#[cfg(not(creusot))]
macro_rules! Ghost {
    ($t:ty) => {creusot_std::prelude::Ghost<()>}
}

pub(crate) use Ghost;
