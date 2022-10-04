# Defaultt

An attempt at formalizing **Default logic** in Coq.

## Default Logic

[**Default Logic**](https://en.wikipedia.org/wiki/Default_logic) is a formal logic initially proposed by Raymond Reiter. It allows to formally reason about *beliefs* and to draw conclusions under uncertainty or incomplete information.

Default Logic has been sucessfully applied to formalize the law as legal reasoning often involves conclusions that are conditioned by numerous exceptions. The [Catala Programming Language](https://cata-lang.org) is an example of project that leverages Default Logic and propose a programming language to formalize the law.

## Coq Formalization

This repository formalize a Propositional Default Logic (an extension of classical propositional logic with defaults). Some fundamental theorems about Default Logic are proved. In particular, we formalize several definitions of **extensions** and prove them equivalents. This lays the basis to prove the correctness of a query engine for Default Logic.