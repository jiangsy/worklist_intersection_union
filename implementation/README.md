# Implementation

## Building Instructions

- **Dependencies**: Require [GHC](https://www.haskell.org/downloads/) and [Stack](https://docs.haskellstack.org/en/stable/README/)
- **Build the project**: navigate to [implementation/](./) directory and run `stack build`.
- **Run the examples**: [examples/](./examples) contains all the examples presented in the paper.
    ```
    stack exec WorklistIntersectionUnion-exe -- <path> [-m]
    ```
    - `<path>`: the path of the input file.
    - `[-m]`: whether considers regard intersection and union of monotypes as monotypes.
    - For example, run `stack exec WorklistIntersectionUnion-exe -- examples/ex12_2.e -m` to show the inference process of file `examples/ex12_2.e` and enable the inference of intersection and union of monotypes.
- **Test all the examples**: To test all the [examples](./examples) presented in the paper (including cases expected to be rejected), please run `stack test`.

## Quick Reference

* Types: `Int`, `Bool`, `Top`, `Bot`, `forall a. Type`, `Type -> Type`, `[Type]`, `Type /\ Type`, `Type \/ Type`, `Label l`
* Int literals: `0`, `1`, `2` ...
* Bool literals: `True` / `False`
* Lambda: `\x -> x`
* Fixpoint: `fix \x -> x`
* Application: `(\x -> x) 1`
* Type annotation: `1 :: Int`
* Type abstraction: `/\a. (\x -> x) :: a -> a`
* Type application: `(\a. (\x -> x) :: a -> a) @Int 3`
* List: `[]` / `1 : 2 : 3 : []` / `True : False : []` ...
* Case: `case lst of [] -> []; (x :: xs) -> ...`
* Let: `let x = 1 in \y -> x` / `let id :: forall (a <: Top). a -> a = /\(a <: Top). \x -> x in id @Int 3` / `letrec map :: ... = ...`

## Quick notes on the implementation

We implemented all the algorithmic rules in the paper. In addition, to make the
examples more interesting we have also implemented a few more simple extensions:

- Polymorphic lists (`[a]`) and a case analysis expression for
pattern matching on lists;
- Recursion via a fixpoint operator;
- Recursive let expressions

All the examples provided in the paper run in our implementation. 
