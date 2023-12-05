
#[cfg(creusot)]
#[macro_export]
macro_rules! info {
  ($($x:tt)*) => {};
}
#[cfg(creusot)]
pub use info;

#[cfg(creusot)]
#[macro_export]
macro_rules! trace {
  ($($x:tt)*) => {};
}
#[cfg(creusot)]
pub use trace;

#[cfg(not(creusot))]
pub use log::{info, trace};