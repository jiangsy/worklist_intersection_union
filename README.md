# #35-Bidirectional Higher-Rank Polymorphism with Intersection and Union Types (Artifact)

Title of the submitted paper: #283-Bidirectional Higher-Rank Polymorphism with Intersection and Union Types

## Overview

The paper discusses three systems: (1). base system; (2). base system with record; (3). base systems with record and intersection/union inference. For brevity, we refer to them as system I, II, and III in the following. (Please refer to Sec 2.3 of the paper for more details).
We believe this artifact is eligible for all three badges: **Available, Functional, and Reusable**.

* **Available** : This artifact is published at zenodo. We agree to publish our artifact under a Creative Commons license.

* **Functional** : The paper has claimed that we formalized the correctness of a type inference algorithm for a system with higher-rank polymorphism, intersection and union types, and explicit type application and provided a prototype implementation. They are all included in this artifact.

  * All the theorems claimed in the paper are formalized in Coq. Please refer to the [Proof](#Proof) section for more details.
  * The implementation includes all the typing rules listed in the paper with some add-ons to type-check some more interesting programs. Please refer to the [Implementation](#Implementation) section for more details.

* **Reusable** : For the proof part, all the raw files to generate the syntactic definitions (by `ott`) and locally-nameless properties (by `lngen`) are provided, as well as the build scripts. Interested users can easily extend them with new syntaxes and features. Coq is also a widely used proof assistant for the PL community. For the implementation part, we provide a full implementation that includes a parser and type-checker. The core function `bigStep` is about 300 LoC Haskell code and easy to modify.

### Component

* `src.zip`: source files of the proof and the implementation
  * `src/proof/`: The whole Coq proof project, which can be compiled with Coq 8.15.2;

    * `src/proof/uni/` Proofs of system I;
    * `src/proof/uni_rec/` Proofs of system II;
    * `src/proof/uni_monoiu/` Proofs of system III;

  * `src/implementation/`: A Haskell implementation of our type inference algorithm capable of running the examples provided in the paper. We implement system I, II, III in a single implementation, with a flag to enable each extension. The implementation will print the algorithmic derivation rules employed during the inference process;
* `docker_image_amd64.zip` docker images for the amd64 platform that pre-install all the dependencies to check the proof and test the implementation;
* `docker_image_arm64.zip` docker images for the arm64 platform that pre-install all the dependencies to check the proof and test the implementation;
* `paper.zip` submission version of the paper and the appendix;

## Proof

The `_.v` file contains all the references to the important lemmas and theorems of each system, including :

  * bidirectional properties: subtyping transitivity (Theorem 3.2, System I, II & III), checking subsumption (Theorem 2.2, System I, II & III), and type safety (Theorem 5.4, System I);
  * bidirectional worklist properties: soundness and completeness (Theorem 5.5, System I, II & III);
  * algorithmic properties: soundness (Theorem 5.6, System I, II & III), completeness (Theorem 5.7, System I, II), and decidability (Theorem 4.2, System I).

The following table (also included in the `appendix.pdf`) illustrates the mapping from all the theorems
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

### Usage

* **Check the proofs**: navigate to the `src/proof/` directory and run `make coq-only`. In case you want to recheck the proof, 
run `make clean-coq-only` first to clean all the previously checked results.
(NOTES: The proof may take a long time to check. For reference, it's about 1 hour on an M2 Max MacBook)

    Expected Output: Definition of each theorem and lemma and axioms used by it. The only axiom used by all the theorems is `Eqdep.Eq_rect_eq.eq_rect_eq`. This
    is introduced by the Coq tactic `dependent destruction` and does not harm the consistency.

    ``` coq
    d_sub_transitivity
        : forall (Ψ : denv) (A B C : typ),
        Ψ ⊢ A <: B -> Ψ ⊢ B <: C -> Ψ ⊢ A <: C
    Axioms:
    Eqdep.Eq_rect_eq.eq_rect_eq
    : forall (U : Type) (p : U) (Q : U -> Type) (x : Q p) (h : p = p),
        x = eq_rect p Q x p h
    d_chk_inf_subsumption
        : forall (n1 n2 n3 : nat) (Ψ Ψ' : denv) (e : exp) 
            (A : typ) (mode : typing_mode),
        uni.decl.prop_typing.exp_size e < n1 ->
        dmode_size mode < n2 ->
        typ_size A < n3 ->
        d_chk_inf Ψ e mode A ->
        d_subtenv Ψ' Ψ ->
        match mode with
        | typingmode__inf => exists A' : typ, Ψ ⊢ A' <: A /\ Ψ' ⊢ e ⇒ A'
        | typingmode__chk => forall A' : typ, Ψ ⊢ A <: A' -> Ψ' ⊢ e ⇐ A'
        end
    Axioms:
    Eqdep.Eq_rect_eq.eq_rect_eq
    : forall (U : Type) (p : U) (Q : U -> Type) (x : Q p) (h : p = p),
        x = eq_rect p Q x p h
    d_chk_inf_elab_sound_f
        : forall (Ψ : denv) (e : exp) (A : typ) (eᶠ : def_ott.fexp)
            (mode : typing_mode),
        d_chk_inf_elab Ψ e mode A eᶠ -> ⟦ Ψ ⟧ ⊢ eᶠ : ᵗ⟦ A ⟧
    Axioms:
    Eqdep.Eq_rect_eq.eq_rect_eq
    : forall (U : Type) (p : U) (Q : U -> Type) (x : Q p) (h : p = p),
        x = eq_rect p Q x p h
    ...
    ```

* **Reproduce the generated code (optional)**: `ott` and `lngen` are used to generate the `def_ott.v` and `prop_ln.v` files already provided in the artifact. You can build all the proofs without these tools installed unless you need to modify the language definitions.  Once installed, use `make clean` to delete the previously generated files. Then executing `make coq` will regenerate the files and check all the proof.

#### Using Docker Images (Recommended)

* Install [docker](https://www.docker.com/)

* Based on your architecture, unzip `docker_image_*.zip` and load the docker image

  `docker load < 35-proof-*.tar.gz`

* Start the container

    `docker run -it 35-proof bash`

* Run the command, e.g., `make coq-only`

#### Building from source

* **Dependencies**: Requires Coq 8.15.2, along with [`Metalib`](https://github.com/plclub/metalib) for the locally nameless infrastructure.
* **Installation guide**: Install Coq 8.15.2 via `opam` (Please refer to the
   [official guide](https://coq.inria.fr/opam-using.html) for detailed steps). After installation, please clone and install [`Metalib`](https://github.com/plclub/metalib) using the following commands:

   ``` bash
   git clone https://github.com/plclub/metalib
   cd metalib/Metalib
   make install
   ```

- (Optional (only if you want to regenerate `def_ott.v` and `prop_ln.v`)) Follow the installation guidelines for [Ott (forked version)](https://github.com/sweirich/ott/tree/ln-close) and [LNgen](https://github.com/plclub/lngen) to install them.

- Run the command, e.g., `make coq-only`


## Implementation

We implemented all the algorithmic rules in the paper. In addition, to make the
examples more interesting we have also implemented a few more simple extensions:

* Polymorphic lists (`[a]`) and a case analysis expression for
pattern matching on lists;
* Recursion via a fixpoint operator;
* Recursive let expressions

All the examples provided in the paper run in this implementation.

### Quick Reference

* Types: `Int`, `Bool`, `Top`, `Bot`, `forall a. Type`, `Type -> Type`, `[Type]`, `Type /\ Type`, `Type \/ Type`, `Label l`
* Int literals: `0`, `1`, `2` ...
* Bool literals: `True` / `False`
* Lambda: `\x -> x`
* Fixpoint: `fix \x -> x`
* Application: `(\x -> x) 1`
* Type annotation: `1 :: Int`
* Type abstraction: `/\a. (\x -> x) :: a -> a`
* Type application: `(/\a. (\x -> x) :: a -> a) @Int 3`
* List: `[]` / `1 : 2 : 3 : []` / `True : False : []` ...
* Case: `case lst of [] -> []; (x :: xs) -> ...`
* Let: `let x = 1 in \y -> x` / `let id :: forall (a <: Top). a -> a = /\(a <: Top). \x -> x in id @Int 3` / `letrec map :: ... = ...`

### Usage

* **Test all the examples**: To test all the examples presented in the paper (including cases expected to be rejected), please run `stack test`.

  Expected Output: The output will show the type-checking results of all the examples. Variant 1 refers to System I and variant 2 refers to System III. `[✔]` at the end of each line means the result is consistent with the result reported in the appendix of the paper (`appendix.pdf`).

  ``` bash
  Variant 1 examples
    ex1_1.e, should be accepted [✔]
    ex1_2.e, should be accepted [✔]
    h1.e, should be accepted [✔]
    f2.e, should be accepted [✔]
    f3_1.e, should be accepted [✔]
    f3_2.e, should be accepted [✔]
    ex4_1.e, should be accepted [✔]
    ex4_2.e, should be accepted [✔]
    ex5_1.e, should be rejected [✔]
    ex5_2.e, should be accepted [✔]
    ex5_3.e, should be rejected [✔]
    ex5_4.e, should be accepted [✔]
    ex6.e, should be accepted [✔]
    ex7_1.e, should be accepted [✔]
    ex7_2.e, should be accepted [✔]
    ex8_1.e, should be accepted [✔]
    ex8_2.e, should be rejected [✔]
    ex8_3.e, should be accepted [✔]
    ex8_4.e, should be rejected [✔]
    h9.e, should be accepted [✔]
    ex9_1.e, should be accepted [✔]
    ex9_2.e, should be accepted [✔]
    ex10.e, should be accepted [✔]
    ex11.e, should be accepted [✔]
    ex12_1.e, should be accepted [✔]
    ex12_2.e, should be accepted [✔]
    ex13.e, should be accepted [✔]
    h14_1.e, should be rejected [✔]
    h14_2.e, should be rejected [✔]
    ex15.e, should be rejected [✔]
  Variant 2 examples
    ex1_1.e, MonoIU on, should be accepted [✔]
    ex1_2.e, MonoIU on, should be accepted [✔]
    h1.e, MonoIU on, should be accepted [✔]
    f2.e, MonoIU on, should be accepted [✔]
    f3_1.e, MonoIU on, should be accepted [✔]
    f3_2.e, MonoIU on, should be accepted [✔]
    ex4_1.e, MonoIU on, should be accepted [✔]
    ex4_2.e, MonoIU on, should be accepted [✔]
    ex5_1.e, MonoIU on, should be rejected [✔]
    ex5_2.e, MonoIU on, should be accepted [✔]
    ex5_3.e, MonoIU on, should be rejected [✔]
    ex5_4.e, MonoIU on, should be accepted [✔]
    ex6.e, MonoIU on, should be accepted [✔]
    ex7_1.e, MonoIU on, should be accepted [✔]
    ex7_2.e, MonoIU on, should be accepted [✔]
    ex8_1.e, MonoIU on, should be accepted [✔]
    ex8_2.e, MonoIU on, should be rejected [✔]
    ex8_3.e, MonoIU on, should be accepted [✔]
    ex8_4.e, MonoIU on, should be accepted [✔]
    h9.e, MonoIU on, should be accepted [✔]
    ex9_1.e, MonoIU on, should be accepted [✔]
    ex9_2.e, MonoIU on, should be accepted [✔]
    ex10.e, MonoIU on, should be accepted [✔]
    ex11.e, MonoIU on, should be accepted [✔]
    ex12_1.e, MonoIU on, should be accepted [✔]
    ex12_2.e, MonoIU on, should be accepted [✔]
    ex13.e, MonoIU on, should be accepted [✔]
    h14_1.e, MonoIU on, should be accepted [✔]
    h14_2.e, MonoIU on, should be rejected [✔]
    ex15.e, MonoIU on, should be rejected [✔]

  Finished in 0.0247 seconds
  60 examples, 0 failures
  ```

* **Run the examples**: `src/implementation/examples/` contains all the examples presented in the paper.

    ``` bash
    stack exec WorklistIntersectionUnion-exe -- <path> [-m]
    ```

  * `<path>`: the path of the input file.
  * `[-m]`: whether regard intersection and union of monotypes as monotypes.
  * For example, run `stack exec WorklistIntersectionUnion-exe -- examples/ex12_2.e -m` to show the inference process of file `examples/ex12_2.e` and enable the inference of intersection and union of monotypes.

#### Using Docker Images (Recommended)
  
* Install [docker](https://www.docker.com/)

* Based on your architecture, unzip `docker_image_*.zip` and load the docker image

  `docker load < 35-implementation-*.tar.gz`

* Start the container

    `docker run -it 35-implementation bash`

* Run the command, e.g., `stack test`

#### Building from source

* **Dependencies**: Require [GHC](https://www.haskell.org/downloads/) and [Stack](https://docs.haskellstack.org/en/stable/README/)
* **Build the project**: navigate to `src/implementation/` directory and run `stack build`.
* Run the command, e.g., `stack test`
