#[cfg(creusot)]
macro_rules! Ghost {
    ($t:ty) => {creusot_contracts::Ghost<$t>}
}

#[cfg(not(creusot))]
macro_rules! Ghost {
    ($t:ty) => {creusot_contracts::Ghost<()>}
}

pub(crate) use Ghost;
