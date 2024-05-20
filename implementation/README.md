# WorklistIntersectionUnion

## Implementation

### Building from Scratch (under directory `src/implementation`)

You need to install GHC first if you wish to build the implementation from scratch:

https://www.haskell.org/downloads/

This project can be built with [Stack](https://docs.haskellstack.org/en/stable/README/).

```
stack build
stack exec WorklistIntersectionUnion-exe <path>
```

### Quick Reference

* Types: `Int`, `Bool`, `Top`, `Bot`, `forall (a <: Type). Type`, `Type -> Type`, `[Type]`
* Int literals: `0`, `1`, `2` ...
* Bool literals: `True` / `False`
* Lambda: `\x -> x`
* Fixpoint: `fix \x -> x`
* Application: `(\x -> x) 1`
* Type annotation: `1 :: Int`
* Type abstraction: `(/\a. \x -> x) :: forall (a <: Top). a -> a`
* Type application: `((/\a. \x -> x) :: forall (a <: Top). a -> a) @Int 3`
* List: `[]` / `1 : 2 : 3 : []` / `True : False : []` ...
* Case: `case lst of [] -> []; (x :: xs) -> ...`
* Let: `let x = 1 in \y -> x` / `let id :: forall (a <: Top). a -> a = /\(a <: Top). \x -> x in id @Int 3`

### Quick notes on the implementation

We implemented all the algorithmic rules in the paper. In addition, to make the
examples more interesting we have also implemented a few more simple extensions:

- Polymorphic lists (`[a]`) and a case analysis expression for
pattern matching on lists;
- Recursion via a fixpoint operator;
- Recursive let expressions

All the examples provided in the paper run in our implementation. 

### Examples

To test all the examples, run

```
stack test
```

Here is an interesting example:

```
let map :: forall (a <: Top). forall (b <: Top). (a -> b) -> [a] -> [b] =
    /\ (a <: Top). /\ (b <: Top). \f -> \xs -> case xs of
                                                [] -> [];
                                                (y : ys) -> f y : map f ys
    in
        let plus = \x -> \y -> 1 in
            let succ = plus 1 in
                map succ (1 : 2 : [])
```

In this example we create the map function on lists, and then apply
it on `map succ (1 : 2 : [])`.
