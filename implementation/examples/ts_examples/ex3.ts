// Finding more about TypeScript's subtyping and solving:

// Subtyping seems to be using unification and a greedy approach, like us:

// This example shows that TypeScript picks the first instantiation greedily
// We are testing if the following holds:
// (1) forall a. a -> a -> a <: {m : number} -> {m : number; n : boolean} -> {m : number}
// (2) forall a. a -> a -> a <: {m : number; n : boolean} -> {m : number} -> {m : number}
//
// With a non-greedy approach both should work. With a greedy approach like ours, 
// only (1) should work. TypeScript only allows (1) to work.

var f33: <A>(x: A) => (y: A) => A = x => y => x
var f34: (x: { m: number }) => (y: { m: number } & { n: boolean }) => { m: number } = f33

// Does not typecheck
// var f35 : (x : {m : number} & {n : boolean}) => (y : {m : number}) => {m : number} = f33

// Is TypeScript's subtyping and solving predicative or impredicative:

// This example seesm to suggest that solving of unifications is impredicative. We can 
// unify:
//
// ^a <: forall a. a -> a
//
// which is not allowed in a predicative approach

var f36: (f: <A>(x: A) => A) => <A>(x: A) => A = id

// Does TypeScript use skolemization?

var f37: <A>(x: number) => (y: A) => A = x => y => y

// It seems that TypeScript does not have skolemization

// var f38 : (x: number) => <A>(y:A) => A = f37

// If I were to guess I would say that they implemented DK's algorithm,
// but allowed solving to be impredicative. 