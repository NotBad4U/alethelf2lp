# Experimental AletheLF translation to Lambdapi

This is an experimental shallow embedding of the AletheLF proof format for SMT solver in Lambdapi.

[AletheLF](https://github.com/cvc5/alfc) (ALF) is a new fine-grained proof format based on [SMT-LIB 3](https://smtlib.cs.uiowa.edu/version3.shtml), which is going to be supported by SMT-solver such as CVC5 in their proof-producing module (such as [CVC5](https://cvc5.github.io/)). This recent format uses a stronger typing system making possible the production of proofs for Bitvector operations, List, or other features that could not be expressed by the current [Alethe](https://verit.gitlabpages.uliege.be/alethe/specification.pdf) proof format. The core language of ALF, [SMT-LIB 3](https://smtlib.cs.uiowa.edu/version3.shtml) theories, are defined as ALF signatures and rewrite rules. Lambdapi is an interactive proof system featuring dependent types like in Martin-Lőf’s type theory, but allows to define objects and types using oriented equations (rewriting rules), and reason modulo those equations.Therefore the native support of rewriting logic and dependent type in Lambdapi make it as a suitable choice for reconstructing ALF proofs due to their closeness proof semantics.

## Content

The shallow embedding can be find [here](alethelf.lp).
Follow the instructions of the lambdapi [manual](https://lambdapi.readthedocs.io/en/latest/getting_started.html#) to install it. 

## References

* [SMTLIB 3](https://smtlib.cs.uiowa.edu/version3.shtml)
* [Alethe user manual](https://github.com/cvc5/alfc/blob/main/user_manual.md)
* [Core.smt3](https://github.com/SMT-LIB/SMT-LIB.github.io/blob/2c5ae03b491c8c66e3570ad5f96940e585ee79c9/Version3/Core.smt3)