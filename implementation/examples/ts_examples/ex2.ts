// Welcome to the TypeScript Playground, this is a website
// which gives you a chance to write, share and learn TypeScript.
function poly<A>(x: A, y: A): A { return x }
var r1 = { m: 1, n: true }
var r2 = { m: 2 }

// This example shows that, for uncurried functions, subtyping constraints 
// are being used. I.e. the approach used for uncurried functions 
// is probably based on local type inference.
var test1 = poly(r1, r2)
var test2 = poly(r2, r1)

// TypeScript supports checking a lambda with a forall
var id: (<A>(x: A) => A) = x => { return x }
var fun: (f: <A>(x: A) => A) => number = f => f(1)

var testfun = fun(x => x)

// TypeScript supports explicit type applications
var testid = id(3)
var testid2 = id<number>(3)

// TypeScript Supports Impredicative Instantiation (I guess that they don't have to worry about decidability)
var testid3 = id(id)

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

var order: (k: <A, B>(x: A) => (y: B) => A) => number = k => k<number, boolean>(3)(true)
var order2: (k: <B, A>(x: A) => (y: B) => A) => number = order

// The following is rejected: another example that breaks subsumption (Example 1 in Elementary Type Inference)
// Basically TypeScript assumes order irrelevant ForallL
// var order3 : (k : <B,A>(x : A) => (y : B) => A) => number = k => k<number,boolean>(3)(true)

var test = order2(x => y => x)

// 
var func: (<A>(f: (x: A) => A) => (x: A) => A) = f => x => f(x)
function func2<A>(f: (x: A) => A, x: A): A { return f(x) }

var testfunc = func(x => x)(1)  // Does not know what to infer
var testfunc2 = func2(x => x, 1) // Correctly infers the type

// From the OOPSLA paper

// It seems that TypeScript adopts a similar approach to us, 
// and it does not allow inference of Top and Bottom (at least in some cases)

function fPlus<A>(f: (x: A) => number, g: (x: A) => number): (x: A) => number { return x => f(x) + g(x) }

// Interestingly, unlike Scala, TypeScript (like us) does not infer bottom for the 
// instantiation below, and the program is rejected.

// var useless = fPlus((x : number) => x + 1, (y: boolean) => 3)

// This is another example from our paper, to illustrate the 
// possible inference of Top. The program below is rejected:

// var testPoly = poly(1,true)

console.log(test)