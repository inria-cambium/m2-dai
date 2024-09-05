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
  + generate_inductive_principle.v, generate_identity.v, generate_indp_proof.v : use cases for the framework
  + ind_closed.v : use case for the extended framework with scope guarantees
  + test_generate_inductive_principle.v, test_identity.v, test_indp_proof.v, test_ind_closed.v : corresponding test files

## Test

Open a test file, such as examples/test_generate_inductive.v, you can define an inductive type `my_type`,

Then the following code defines a Coq term with name `"my_indp"` which is the (type of) induction principle of `my_type`.

```
MetaCoq Run Derive InductivePrinciple my_type as "my_indp".
```

