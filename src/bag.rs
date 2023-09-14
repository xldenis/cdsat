// use creusot_contracts::*;

// #[creusot::builtins = "bag.Bag.bag"]
// pub struct Bag<T: ?Sized>(::std::marker::PhantomData<T>);

// impl<T: ?Sized> Bag<T> {
//     #[trusted]
//     #[creusot::builtins = "bag.Bag.empty_bag"]
//     pub const EMPTY: Self = { Bag(::std::marker::PhantomData) };

//     #[trusted]
//     #[ghost]
//     #[creusot::builtins = "bag.Bag.singleton"]
//     pub fn singleton(_ : T) -> Self {
//         absurd
//     }

//     #[predicate]
//     #[why3::attr = "inline:trivial"]
//     pub fn contains(self, e: T) -> bool {
//         Self::mem(e, self)
//     }

//     #[trusted]
//     #[ghost]
//     #[creusot::builtins = "bag.Bag.mem"]
//     fn mem(_: T, _: Self) -> bool {
//         pearlite! { absurd }
//     }

//     #[ghost]
//     #[why3::attr = "inline:trivial"]
//     pub fn insert(self, e: T) -> Self {
//         Self::add(e, self)
//     }

//     #[trusted]
//     #[ghost]
//     #[creusot::builtins = "bag.Bag.add"]
//     fn add(_: T, _: Self) -> Self {
//         pearlite! { absurd }
//     }

//     #[trusted]
//     #[predicate]
//     #[creusot::builtins = "bag.Bag.is_empty"]
//     pub fn is_empty(self) -> bool {
//         pearlite! { absurd }
//     }

//     #[trusted]
//     #[ghost]
//     #[creusot::builtins = "bag.Bag.diff"]
//     pub fn diff(self, _: Self) -> Self {
//         pearlite! { absurd}
//     }

//     #[trusted]
//     #[ghost]
//     #[creusot::builtins = "bag.Bag.union"]
//     pub fn union(self, _: Self) -> Self {
//         pearlite! { absurd}
//     }

//     #[trusted]
//     #[ghost]
//     #[creusot::builtins = "bag.Bag.card"]
//     pub fn len(self) -> Int {
//         pearlite! { absurd }
//     }

//     #[trusted]
//     #[ghost]
//     #[creusot::builtins = "bag.Bag.inter"]
//     pub fn inter(self, _ : Self) -> Self {
//       absurd
//     }

//     #[trusted]
//     #[ghost]
//     #[creusot::builtins = "bag.Bag.choose"]
//     pub fn pick(self) -> T
//     where T : Sized {
//       absurd
//     }

//     #[predicate]
//     pub fn is_set(self) -> bool
//     where T : Sized {
//         pearlite! { forall<a : T> self.count(a) <= 1 }
//     }

//     #[ghost]
//     #[why3::attr = "inline:trivial"]
//     pub fn count(self, e : T) -> Int {
//         Self::nb_occ(e, self)
//     }

//     #[trusted]
//     #[ghost]
//     #[creusot::builtins = "bag.Bag.nb_occ"]
//     fn nb_occ(_ : T, _: Self) -> Int {
//         absurd
//     }
// }
