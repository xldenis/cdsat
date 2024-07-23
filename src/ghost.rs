macro_rules! Ghost {
    ($t:ty) => {creusot_contracts::Snapshot<$t>}
}



pub(crate) use Ghost;
