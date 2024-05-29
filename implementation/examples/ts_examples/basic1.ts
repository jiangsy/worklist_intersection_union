// Testing the power of matching in TypeScript

// Basic Matching

function f1(x: number & Boolean): number { return (x + 1) };

function f2(o: { m: number, n: boolean }): number { return o.m }

// TypeScript checks for well-formed records (cannot have duplicated labels)
// function f2a(o : {m : number, m : string}) : number{return o.m}

function f3(o: { m: number, n: boolean } & { k: string }): number { return o.m }

function f4(o: { m: number, n: boolean } & { k: string }): number { return o.m }

// Rejected
// function f5(o : {m : number, n : Boolean} | {k : string}) : number {return o.m}

// function f5(o : {m : number, n : Boolean} | {k : string}) : number {return o.m}

function f5(o: { m: number, n: boolean } | { k: string, m: number }): number { return o.m }

// Overloading

function f6(f: ((i: number) => number) & ((b: boolean) => boolean)): boolean { return f(true) }

// Picks the first match in the overload: the following works
function f7(f: ((i1: number) => (i2: number) => number) & ((i: number) => (b: boolean) => boolean)) { return f(1)(2) }

// Picks the first match in the overload: the following does not work
// function f8(f : ((i1 :number) => (i2 : number) => number) & ((i : number) => (b : boolean) => boolean))  {return f(1)(true)}

// function f9(f : ((i1 :number) => (i2 : number) => number) & ((i : number) => (b : boolean) => boolean)) : (b : boolean) => boolean {return f(1)}

// Return type overloading: chooses the 2nd overload, I guess, here

function f10(f: ((i: number) => number) & ((i: number) => boolean)) { return true && f(1) }

// Generics and instantiation

function f11<R>(o: { m: number } & R): R { return o }

var testf11a = f11({ m: 1 })  // infers unknown instead of any (Top) for the instantiation for some reason

var testf11b = f11({ m: 1, n: true })

function f12<R>(o: ({ m: number } & R) | R): R { return o }

var testf12a = f12({ m: 1 })  // infers unknown instead of any (Top) for the instantiation for some reason