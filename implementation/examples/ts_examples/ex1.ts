function poly<A>(x: A, y: A): A { return x }
var r1 = { m: 1, n: true }
var r2 = { m: 2 }

// This example shows that, for uncurried functions, subtyping constraints 
// are being used. I.e. the approach is probably based on local type inference.
var test1 = poly(r1, r2)
var test2 = poly(r2, r1)

// TypeScript supports checking a lambda with a forall
var id: (<A>(x: A) => A) = x => { return x }
var fun: (f: <A>(x: A) => A) => number = f => f(1)

var testfun = fun(x => x)

// TypeScript supports explicit type applications
var testid = id(3)
var testid2 = id<number>(3)

var poly2: <A>(x: A) => (y: A) => A = x => y => { return y }

// Instantiation for curried functions is greedy
// The first example fails.

// var test3 = poly2(r1)(r2)
var test4 = poly2(r2)(r1)

// Examples from the Elementary Type Inference Paper
var hpoly = (f: <A>(x: A) => A) => [f(1), f(true)]

// var foo : (f : <A>A) => number = 

// Typescript has the same problem that was identified in 
// Elementary Type Inference for GHC 8
//
// TypeScript does not have the subsumption property!

var f: (k: <A>(x: number) => (y: A) => number) => (b: boolean) => number = k => k(3)
var h: (k: <A, B>(x: B) => (y: A) => B) => (b: boolean) => number = k => f(k)
var g: (k: <A>(x: number) => (y: A) => number) => (b: boolean) => number = k => k<boolean>(3)

var h2: (k: <A, B>(x: B) => (y: A) => B) => (b: boolean) => number = k => g(k)

// The following is rejected, exactly the same issue detected in the Elementary type inference paper
// var h3 : (k : <A,B>(x : B) => (y:A) => B) => (b : boolean) => number = k => k<boolean>(3)