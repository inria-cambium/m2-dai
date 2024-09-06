## Installation


### Requirement

The Coq Proof Assistant, version 8.19.1

The MetaCoq, version 1.3.1+8.19

Installing the correct version with OPAM:
```
# opam install coq-metacoq.1.3.1+8.19
```

For no OPAM users, please check https://github.com/MetaCoq/metacoq/blob/main/INSTALL.md

### Getting the source
```
# git clone git@github.com:inria-cambium/m2-dai.git
```

### Compiling from source
At the main root of the project, use:
```
# make
```

## Overview
- theories
  + Programming : framework for simplifying the meta-programming with MetaCoq
    - BasePrelude.v: API
    - ParamChecker.v: API for checking (non-)uniform parameter
  + ScopedProgramming: extended framework for meta-programming with scope guarantees

- examples

  use cases for the 1st framework:
  + identity : deriving the identity function of any inductive type
  + induction_principle : deriving the induction principle (just type, no proof term) of any inductive type
  + induction_principle_proof : deriving the induction principle (proof term) of any inductive type

  use case for the extended framework with scope guarantees:
  + induction_principle_closed : deriving the induction principle (just type, no proof term) of any inductive type

## Test

Open a test file, such as examples/induction_principle/test_generate_inductive.v, you can define an inductive type `my_type`,

Then the following code defines a Coq term with name `"my_indp"` which is the (type of) induction principle of `my_type`.

```
MetaCoq Run Derive InductivePrinciple my_type as "my_indp".
```
