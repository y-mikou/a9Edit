# crates

This directory contains the crates that make up a9Edit and its supporting tooling.

* `a9edit` (`a9Edit/`): Main editor binary and library<br>
  It is split apart into a library to allow for benchmarks.
* `lsh`: Syntax-highlighting compiler and runtime
* `lsh-bin`: A small CLI for experimenting with and debugging LSH output
* `stdext`: Shared utility code used across the workspace
* `unicode-gen`: Code generation utilities for Unicode LUTs
