# Bidirectional Higher-Rank Polymorphism with Intersection and Union Types (Artifact)

Title of the submitted paper: Bidirectional Higher-Rank Polymorphism with Intersection and Union Types

## Overview

* [proof/](./proof): The whole Coq proof project, which can be compiled with Coq 8.15.2.
* [implementation/](./implementation): A Haskell implementation of our type inference algorithm capable of running the examples provided in the paper. The implementation will print the algorithmic derivation rules employed during the inference process.

## Getting Started

### Proofs

#### Building Instructions

- **Dependencies**: Requires Coq 8.15.2, along with [`Metalib`](https://github.com/plclub/metalib) for the locally nameless
- **Installation guide**: Install Coq 8.15.2 via `opam` (Please refer to the
   [official guide](https://coq.inria.fr/opam-using.html) for detailed steps). After instalation, please clone and install [`Metalib`](https://github.com/plclub/metalib) using the following commands:
   ```
   git clone https://github.com/plclub/metalib
   cd metalib/Metalib
   make install
   ```
- **Build the proofs**: navigate to [proof/](./proof) directory and run `make coq`. The full compilation usually takes more than 1 hour. After it ends, it will print all the axioms.
- **Reproduce the generated code (optional)**: `ott` and `lngen` are used to generate the `def_ott.v` and `prop_ln.v` files already provided in the artifact. You can build all the proofs without these tools installed unless you need to modify the language definitions. In that cases you can follow the installation guidelines for [Ott (forked version)](https://github.com/sweirich/ott/tree/ln-close) and [LNgen](https://github.com/plclub/lngen). Once installed, use `make clean` to delete the previously generated files. Then executing `make coq` will regenerate the files.

### Implementation

#### Building Instructions

- **Dependencies**: Require [GHC](https://www.haskell.org/downloads/) and [Stack](https://docs.haskellstack.org/en/stable/README/)
- **Build the project**: navigate to [implementation/](./implementation) directory and run `stack build`.
- **Run the examples**: [implementation/examples/](./implementation/examples) contains all the examples presented in the paper.
    ```
    stack exec WorklistIntersectionUnion-exe -- <path> [-m]
    ```
    - `<path>`: the path of the input file.
    - `[-m]`: whether considers regard intersection and union of monotypes as monotypes.
    - For example, run `stack exec WorklistIntersectionUnion-exe -- examples/ex12_2.e -m` to show the inference process of file `examples/ex12_2.e` and enable the inference of intersection and union of monotypes.
- **Test all the examples**: To test all the examples presented in the paper (including cases expected to be rejected), please run `stack test`.

#### Quick Reference

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

#### Quick notes on the implementation

We implemented all the algorithmic rules in the paper. In addition, to make the
examples more interesting we have also implemented a few more simple extensions:

- Polymorphic lists (`[a]`) and a case analysis expression for
pattern matching on lists;
- Recursion via a fixpoint operator;
- Recursive let expressions

All the examples provided in the paper run in our implementation. 

## Correspondence between paper and Coq proofs

### Definitions

The table in the appendix of the submission illustrates the mapping from the theorems
in the paper to their corresponding theorem names in the Coq proof.

### Lemmas and Theorems


| Symbol      | Coq name                                                                                                     |
| ----------- | ------------------------------------------------------------------------------------------------------------ |
| Theorem 2.1 | `d_sub_inst`                                                                                                 |
| Theorem 2.2 | `d_chk_subsumption`                                                                                          |
| Theorem 3.1 | `d_sub_reflexivity`                                                                                          |
| Theorem 3.2 | `d_sub_transitivity`                                                                                         |
| Lemma 3.3   | `d_infabs_soundness`, `d_infabs_completeness`                                                                |
| Lemma 3.4   | `d_inftapp_soundness1`, `d_inftapp_completeness`                                                             |
| Theorem 4.1 | `a_wl_red_chk_soundness`, `a_wl_red_inf_soundness`, `a_wl_red_chk_completeness`, `a_wl_red_inf_completeness` |
| Theorem 4.2 | `a_wf_wl_red_decidable_thm`                                                                                  |
| Theorem 5.1 | `d_sub_subst_stvar`                                                                                          |
| Theorem 5.2 | `d_infabs_subsumption_same_env`, `d_inftapp_subsumption_same_env`                                            |
| Theorem 5.3 | `d_chk_inf_subsumption`                                                                                      |
| Theorem 5.4 | `d_chk_inf_elab_sound_f`                                                                                     |
| Theorem 5.5 | `d_wl_red_sound`, `d_wl_red_complete`                                                                        |
| Theorem 5.6 | `a_wl_red_soundness`                                                                                         |
| Theorem 5.7 | `a_wl_red_completeness`                                                                                      |
| Lemma 5.8   | `aworklist_subst_transfer_same_dworklist_rev`, `aworklist_subst_transfer_same_dworklist`                     |
| Lemma 5.9   | `trans_typ_etvar_s_in_more_num_arrow`, `d_sub_more_num_arrow_in_mono_typ`                                    |
