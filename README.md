# KEM Binding in EasyCrypt

This repository contains an EasyCrypt development aimed at the formal verification of the [binding properties](https://eprint.iacr.org/2023/1933) of [ML-KEM](https://doi.org/10.6028/NIST.FIPS.203) and the Fujisaki-Okamoto transform&ndash;or, rather, [the modular revision of this transform by Hofheinz, Hövelmanns, and Kiltz](https://eprint.iacr.org/2017/604), which is accompanied by a security analysis against quantum adversaries.

Initially, this repository also contained comprehensive libraries for Key Encapsulation Mechanisms (KEMs) and Public-Key Encryption (PKE) schemes, generically defining the constructions as well as their properties and corresponding relations, including those in the Random Oracle Model (ROM). These libraries were constructed as an initial endeavor in this project, but [have since been integrated into EasyCrypt itself](https://github.com/EasyCrypt/easycrypt/tree/main/theories/crypto).

What follows is an overview of the directories and files in this repository (related to the EasyCrypt development).

- `archive/`: Archived/Deprecated files (that might still be useful for quick reference).
- `proofs/`: Main proof scripts
  - `FO_T.eca`: Formalization and analysis of the T transform. (Currently in very early stages of development and doesn't contain much of substance yet.)
  - `FO_U.eca`: Formalization and analysis of the (four variants of the) U transform.
  - `HashFunctions.eca`: "Library" formalizing hash functions and their security properties. (Currently very minimal and only contains what is needed for other proofs.)
  - `KEM_KDF_PP`: Formalization and analysis of transforms that recompute the shared secret of a KEM by post-processing some of its outputs using a collision-resistant hash function.
  - `KeyEncapsulationMechanismROMx2.eca`: "Library" formalizing KEMs considering two random oracles and their security properties. (Currently very minimal and only contains what is needed for other proofs.)
  - `ML_KEM_HL_Binding.eca`: Formalization and analysis of ML-KEM (on a high-level).
  - `ROMx2.eca`: Formalization and analysis of scenarios dealing with two independent random oracles at the same time, particularly concerning the probability of collisions between them.

There's a writeup of this work [here](./docs/keeping-up-with-the-kems-formally-easycrypt-edition.md)