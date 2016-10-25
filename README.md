# hs2agda

Note: The work described in this README is aspirational and incomplete.

`hs2agda` is a tool for the formal verification of Haskell code. It converts
Haskell source code to the equivalent Agda representation, which maintains the
semantics while allowing for formal reasoning and proofs about program behavior.

It is based on ideas from the
paper ["Verifying Haskell Programs Using Constructive Type Theory"][paper].

This is a fork of the CoverTranslator project, focused on the `hs2agda` component. 
The original code targeted Agda 1, while this fork will target Agda 2. The
first commit to this repo was a faithful copy of CoverTranslator v0.3.

## License

The original CoverTranslator project was licensed under the MIT license, and
this code retains those terms and the copyright notice.

[paper]: http://www2.tcs.ifi.lmu.de/~abel/haskell05.pdf
