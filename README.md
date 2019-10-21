# Continuous π-calculus

This is a machine formalisation of the [Continuous π-calculus][cpi], using the
[Lean theorem prover][lean].

## Building
 - If you do not have Lean installed, use [elan][elan] to install the
   appropriate version.
 - Run `leanpkg build` within the root directory of the project. All
   dependencies should be installed, and the project type-checked.

[cpi]: http://homepages.inf.ed.ac.uk/stark/continuous-pi.html
[lean]: https://leanprover.github.io/
[elan]: https://github.com/Kha/elan
